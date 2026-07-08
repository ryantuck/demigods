#!/usr/bin/env python3
"""Generate mock bank data for the budget tracker.

Writes two CSVs into data/:
  - checking.csv     (mimics a typical bank export: Date, Description, Amount, Balance)
  - credit_card.csv  (mimics a card statement export: Transaction Date, Post Date, Description, Category Hint, Amount)

Amount conventions match real exports:
  - checking: negative = money out, positive = money in
  - credit card: positive = charge, negative = payment/credit

Deterministic (seeded) so the committed CSVs are reproducible.
"""

import csv
import random
from datetime import date, timedelta
from pathlib import Path

SEED = 20260101
START = date(2026, 1, 1)
END = date(2026, 6, 30)

OUT_DIR = Path(__file__).parent / "data"


def month_days(d: date) -> list[date]:
    days = []
    cur = d.replace(day=1)
    while cur.month == d.month:
        days.append(cur)
        cur += timedelta(days=1)
    return days


def iter_months(start: date, end: date):
    cur = start.replace(day=1)
    while cur <= end:
        yield cur
        cur = (cur + timedelta(days=32)).replace(day=1)


def business_day_on_or_after(d: date) -> date:
    while d.weekday() >= 5:
        d += timedelta(days=1)
    return d


def gen_checking(rng: random.Random) -> list[dict]:
    rows = []

    def add(d, desc, amount):
        rows.append({"date": d, "desc": desc, "amount": round(amount, 2)})

    # Biweekly paychecks, two earners
    pay = START + timedelta(days=1)  # Jan 2
    while pay <= END:
        add(business_day_on_or_after(pay), "DIRECT DEP ACME CORP PAYROLL", 3184.62)
        pay += timedelta(days=14)
    pay = START + timedelta(days=8)  # Jan 9
    while pay <= END:
        add(business_day_on_or_after(pay), "DIRECT DEP RIVERSIDE SCHOOL DIST PAY", 2291.15)
        pay += timedelta(days=14)

    for m in iter_months(START, END):
        # Mortgage: fixed, on the 1st
        add(business_day_on_or_after(m), "FIRSTBANK MORTGAGE PMT 0031877", -2418.00)
        # Escrow-external bills
        add(m.replace(day=5), "CITY WATER & SEWER AUTOPAY", -rng.uniform(58, 84))
        add(m.replace(day=12), "NORTHERN GRID ELECTRIC BILLPAY", -rng.uniform(96, 210))
        add(m.replace(day=12), "VALLEY GAS UTILITY", -rng.uniform(40, 165) if m.month <= 4 else -rng.uniform(24, 42))
        add(m.replace(day=18), "COMCAST XFINITY INTERNET", -89.99)
        add(m.replace(day=20), "TMOBILE AUTOPAY", -140.00)
        # Insurance & childcare
        add(m.replace(day=3), "STATE FARM INSURANCE AUTO+UMBRELLA", -212.40)
        add(m.replace(day=15), "LITTLE SPROUTS DAYCARE ACH", -1450.00)
        # Retirement / savings transfer (internal — should be tracked as savings, not spending)
        add(m.replace(day=6), "ONLINE XFER TO SAVINGS XXXX4821", -800.00)
        # Credit card payment (must be EXCLUDED by the processor to avoid double counting)
        add(m.replace(day=25), "CHASE CREDIT CRD EPAY", -rng.uniform(2300, 3400))
        # Occasional checking-side spending
        if rng.random() < 0.7:
            add(m.replace(day=rng.randint(8, 26)), "ATM WITHDRAWAL MAIN ST", -rng.choice([40, 60, 80, 100]))
        if rng.random() < 0.5:
            add(m.replace(day=rng.randint(10, 24)), "CHECK 10%02d GREEN LAWN CARE" % rng.randint(1, 99), -rng.uniform(45, 120))
        if m.month == 4:
            add(m.replace(day=14), "IRS USATAXPYMT", -1240.00)
        if m.month == 3:
            add(m.replace(day=22), "VENMO CASHOUT", 180.00)

    rows.sort(key=lambda r: r["date"])
    # Running balance, like a real export
    balance = 6243.19
    out = []
    for r in rows:
        balance = round(balance + r["amount"], 2)
        out.append({
            "Date": r["date"].strftime("%m/%d/%Y"),
            "Description": r["desc"],
            "Amount": f"{r['amount']:.2f}",
            "Balance": f"{balance:.2f}",
        })
    return out


CARD_MERCHANTS = [
    # (weight, description template, category hint from the issuer, (lo, hi))
    (10, "WHOLEFDS MKT #{n4}", "Groceries", (48, 215)),
    (8,  "TRADER JOE'S #{n3}", "Groceries", (32, 130)),
    (6,  "COSTCO WHSE #{n4}", "Groceries", (95, 320)),
    (7,  "SHELL OIL {n8}", "Gas", (28, 72)),
    (3,  "EXXONMOBIL {n8}", "Gas", (30, 68)),
    (6,  "CHIPOTLE {n4}", "Food & Drink", (24, 52)),
    (5,  "LUIGI'S TRATTORIA", "Food & Drink", (58, 145)),
    (6,  "DOORDASH*VARIOUS", "Food & Drink", (28, 74)),
    (7,  "STARBUCKS STORE {n5}", "Food & Drink", (6, 19)),
    (8,  "AMAZON.COM*{a7}", "Shopping", (12, 180)),
    (4,  "TARGET T-{n4}", "Shopping", (25, 160)),
    (2,  "HOMEDEPOT.COM", "Home Improvement", (35, 260)),
    (3,  "CVS/PHARMACY #{n5}", "Health", (8, 65)),
    (2,  "WALGREENS #{n4}", "Health", (10, 45)),
    (2,  "KIDS PEDIATRIC ASSOC COPAY", "Health", (25, 40)),
]

CARD_SUBSCRIPTIONS = [
    ("NETFLIX.COM", "Entertainment", 15.49, 6),
    ("SPOTIFY USA", "Entertainment", 16.99, 3),
    ("DISNEYPLUS", "Entertainment", 13.99, 9),
    ("NYTIMES*SUBSCRIPTION", "News", 17.00, 12),
    ("PELOTON* MEMBERSHIP", "Health", 44.00, 17),
    ("GOOGLE *STORAGE", "Services", 9.99, 21),
]


def fill_tokens(rng: random.Random, template: str) -> str:
    for token, width in (("{n3}", 3), ("{n4}", 4), ("{n5}", 5), ("{n8}", 8)):
        while token in template:
            template = template.replace(token, "".join(rng.choice("0123456789") for _ in range(width)), 1)
    while "{a7}" in template:
        template = template.replace("{a7}", "".join(rng.choice("A0B1C2D3E4F5G6H7") for _ in range(7)), 1)
    return template


def gen_credit_card(rng: random.Random) -> list[dict]:
    rows = []

    def add(d, desc, hint, amount):
        rows.append({"date": d, "desc": desc, "hint": hint, "amount": round(amount, 2)})

    weights = [m[0] for m in CARD_MERCHANTS]
    day = START
    while day <= END:
        # ~2.2 swipes/day on average, weekend-skewed
        n = rng.choices([0, 1, 2, 3, 4], weights=[18, 30, 26, 16, 10])[0]
        if day.weekday() >= 5:
            n += rng.choice([0, 1, 1])
        for _ in range(n):
            _, tmpl, hint, (lo, hi) = rng.choices(CARD_MERCHANTS, weights=weights)[0]
            add(day, fill_tokens(rng, tmpl), hint, rng.uniform(lo, hi))
        day += timedelta(days=1)

    for m in iter_months(START, END):
        for desc, hint, amount, dom in CARD_SUBSCRIPTIONS:
            add(m.replace(day=dom), desc, hint, amount)
        # Statement payment (a credit — must be excluded from spending)
        add(m.replace(day=25), "AUTOMATIC PAYMENT - THANK YOU", "Payment", -rng.uniform(2300, 3400))

    # A few one-offs that make the data interesting
    add(date(2026, 2, 13), "DELTA AIR 0062341998877", "Travel", 428.40)
    add(date(2026, 2, 13), "DELTA AIR 0062341998878", "Travel", 428.40)
    add(date(2026, 3, 20), "MARRIOTT SAVANNAH RIVERFRONT", "Travel", 612.88)
    add(date(2026, 3, 21), "HERTZ RENT-A-CAR SAV", "Travel", 187.25)
    add(date(2026, 5, 4), "BEST BUY #0442", "Shopping", 899.99)
    add(date(2026, 6, 11), "PETSMART #1183", "Shopping", 84.17)
    add(date(2026, 1, 28), "AMAZON.COM REFUND", "Shopping", -43.12)

    rows.sort(key=lambda r: r["date"])
    return [
        {
            "Transaction Date": r["date"].strftime("%m/%d/%Y"),
            "Post Date": (r["date"] + timedelta(days=rng.choice([1, 1, 2]))).strftime("%m/%d/%Y"),
            "Description": r["desc"],
            "Category": r["hint"],
            "Amount": f"{r['amount']:.2f}",
        }
        for r in rows
    ]


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {path} ({len(rows)} rows)")


def main() -> None:
    OUT_DIR.mkdir(exist_ok=True)
    rng = random.Random(SEED)
    write_csv(OUT_DIR / "checking.csv", gen_checking(random.Random(SEED)))
    write_csv(OUT_DIR / "credit_card.csv", gen_credit_card(random.Random(SEED + 1)))


if __name__ == "__main__":
    main()
