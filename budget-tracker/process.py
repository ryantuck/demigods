#!/usr/bin/env python3
"""Categorize checking + credit card transactions into a spending summary.

Reads data/checking.csv and data/credit_card.csv, applies merchant keyword
rules, and writes:
  - summary.json  — the full categorized summary
  - data.js       — the same object as `window.BUDGET_DATA` so index.html
                    works when opened directly via file:// (no fetch/CORS)

Also prints a monthly report to stdout.

Double-count guard: credit card purchases are counted from the card
statement, so the card *payments* that appear in both files (checking debit,
card credit) are classified as Transfer and excluded from spending. The same
goes for savings transfers — they're tracked separately, not as spending.
"""

import csv
import json
from collections import defaultdict
from datetime import datetime
from pathlib import Path

BASE = Path(__file__).parent

# First matching rule wins; keys are substrings of the uppercased description.
# kind: "spend" | "income" | "savings" | "transfer" (transfer = ignored)
RULES = [
    # --- non-spending flows first, so they can't fall into a spend bucket ---
    (["CREDIT CRD EPAY", "AUTOMATIC PAYMENT", "CARDMEMBER SERV"], "Transfer", "transfer"),
    (["XFER TO SAVINGS"], "Savings", "savings"),
    (["DIRECT DEP", "PAYROLL", "VENMO CASHOUT"], "Income", "income"),
    (["REFUND"], "Refund", "spend"),  # negative amount → reduces its month's spending
    # --- spending categories ---
    (["MORTGAGE"], "Mortgage", "spend"),
    (["WATER & SEWER", "ELECTRIC", "GAS UTILITY", "XFINITY", "TMOBILE", "COMCAST"], "Utilities", "spend"),
    (["INSURANCE", "STATE FARM"], "Insurance", "spend"),
    (["DAYCARE", "LITTLE SPROUTS"], "Childcare", "spend"),
    (["WHOLEFDS", "TRADER JOE", "COSTCO", "KROGER", "SAFEWAY"], "Groceries", "spend"),
    (["CHIPOTLE", "TRATTORIA", "DOORDASH", "STARBUCKS", "GRUBHUB", "MCDONALD"], "Dining", "spend"),
    (["SHELL OIL", "EXXON", "CHEVRON", "BP#", "UBER", "LYFT", "PARKING"], "Transportation", "spend"),
    (["NETFLIX", "SPOTIFY", "DISNEYPLUS", "HULU", "NYTIMES", "PELOTON", "GOOGLE *STORAGE"], "Subscriptions", "spend"),
    (["CVS", "WALGREENS", "PHARMACY", "PEDIATRIC", "DENTAL", "MEDICAL"], "Health", "spend"),
    (["DELTA AIR", "UNITED", "MARRIOTT", "HILTON", "AIRBNB", "HERTZ"], "Travel", "spend"),
    (["AMAZON", "TARGET", "BEST BUY", "HOMEDEPOT", "PETSMART", "WALMART"], "Shopping", "spend"),
    (["IRS", "USATAXPYMT"], "Taxes", "spend"),
]
FALLBACK = ("Other", "spend")  # ATM withdrawals, checks, anything unmatched


def categorize(description: str) -> tuple[str, str]:
    desc = description.upper()
    for keywords, category, kind in RULES:
        if any(k in desc for k in keywords):
            return category, kind
    return FALLBACK


def load_checking(path: Path) -> list[dict]:
    txns = []
    with path.open() as f:
        for row in csv.DictReader(f):
            txns.append({
                "date": datetime.strptime(row["Date"], "%m/%d/%Y").date(),
                "description": row["Description"],
                # checking: negative = out. Normalize to positive = money spent.
                "amount": -float(row["Amount"]),
                "account": "checking",
            })
    return txns


def load_credit_card(path: Path) -> list[dict]:
    txns = []
    with path.open() as f:
        for row in csv.DictReader(f):
            txns.append({
                "date": datetime.strptime(row["Transaction Date"], "%m/%d/%Y").date(),
                "description": row["Description"],
                # card: positive = charge, already "money spent"
                "amount": float(row["Amount"]),
                "account": "credit_card",
            })
    return txns


def build_summary(txns: list[dict]) -> dict:
    months = sorted({t["date"].strftime("%Y-%m") for t in txns})
    by_month_cat = defaultdict(lambda: defaultdict(float))
    totals = defaultdict(float)
    income_by_month = defaultdict(float)
    savings_by_month = defaultdict(float)
    categorized = []

    for t in txns:
        category, kind = categorize(t["description"])
        month = t["date"].strftime("%Y-%m")
        categorized.append({**t, "date": t["date"].isoformat(), "category": category, "kind": kind})
        if kind == "transfer":
            continue
        if kind == "income":
            income_by_month[month] += -t["amount"]  # income arrives as negative "spend"
        elif kind == "savings":
            savings_by_month[month] += t["amount"]
        else:
            # Refunds land here with negative amounts and offset their category month
            target = "Shopping" if category == "Refund" else category
            by_month_cat[month][target] += t["amount"]
            totals[target] += t["amount"]

    spending_by_month = {m: round(sum(cats.values()), 2) for m, cats in by_month_cat.items()}
    category_totals = sorted(
        ({"category": c, "total": round(v, 2)} for c, v in totals.items()),
        key=lambda x: -x["total"],
    )

    return {
        "generated_from": ["data/checking.csv", "data/credit_card.csv"],
        "period": {"start": months[0], "end": months[-1]},
        "months": months,
        "income_by_month": {m: round(income_by_month[m], 2) for m in months},
        "savings_by_month": {m: round(savings_by_month[m], 2) for m in months},
        "spending_by_month": {m: spending_by_month.get(m, 0.0) for m in months},
        "by_month_category": {
            m: {c: round(v, 2) for c, v in sorted(by_month_cat[m].items())} for m in months
        },
        "category_totals": category_totals,
        "totals": {
            "income": round(sum(income_by_month.values()), 2),
            "spending": round(sum(spending_by_month.values()), 2),
            "savings_transfers": round(sum(savings_by_month.values()), 2),
        },
        "transaction_count": len(categorized),
        "transactions": categorized,
    }


def print_report(s: dict) -> None:
    w = 15
    print(f"\nHousehold spending summary  {s['period']['start']} .. {s['period']['end']}")
    print("=" * 66)
    for m in s["months"]:
        inc, spend, save = s["income_by_month"][m], s["spending_by_month"][m], s["savings_by_month"][m]
        print(f"\n{m}   income {inc:>10,.2f}   spending {spend:>10,.2f}   saved {inc - spend:>9,.2f}")
        for cat, v in sorted(s["by_month_category"][m].items(), key=lambda kv: -kv[1]):
            print(f"    {cat:<{w}} {v:>10,.2f}")
        print(f"    {'(to savings acct)':<{w}} {save:>10,.2f}")
    t = s["totals"]
    print("\n" + "=" * 66)
    print(f"TOTAL   income {t['income']:>12,.2f}   spending {t['spending']:>12,.2f}")
    net = t["income"] - t["spending"]
    print(f"        net {net:>+15,.2f}   savings rate {net / t['income']:.1%}")


def main() -> None:
    txns = load_checking(BASE / "data" / "checking.csv") + load_credit_card(BASE / "data" / "credit_card.csv")
    summary = build_summary(txns)

    (BASE / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (BASE / "data.js").write_text(
        "// Generated by process.py — do not edit by hand.\n"
        "window.BUDGET_DATA = " + json.dumps(summary, indent=2) + ";\n"
    )
    print(f"wrote summary.json and data.js ({summary['transaction_count']} transactions)")
    print_report(summary)


if __name__ == "__main__":
    main()
