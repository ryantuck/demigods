# Household Budget Tracker

A roll-your-own budget tracker: mock bank exports → categorized spending
summary → static HTML dashboard. No dependencies beyond the Python standard
library; the dashboard is a single self-contained page you can open from disk.

## Pipeline

```
generate_mock_data.py ──▶ data/checking.csv        ┐
                          data/credit_card.csv     ├──▶ process.py ──▶ summary.json
                                                   ┘                   data.js ──▶ index.html
```

1. **`generate_mock_data.py`** — writes six months (Jan–Jun 2026) of
   deterministic, seeded mock data in the shape of real bank exports:
   - `data/checking.csv` — `Date, Description, Amount, Balance` (negative =
     money out). Biweekly paychecks for two earners, a fixed mortgage payment,
     utilities, insurance, daycare, a monthly savings transfer, and the monthly
     credit card payment.
   - `data/credit_card.csv` — `Transaction Date, Post Date, Description,
     Category, Amount` (positive = charge). Groceries, dining, gas,
     subscriptions, shopping, plus a few one-off trips and purchases.

2. **`process.py`** — loads both CSVs, categorizes each transaction with
   first-match-wins merchant keyword rules, and writes `summary.json` plus
   `data.js` (the same object as `window.BUDGET_DATA`, so `index.html` works
   over `file://` without a server). It also prints a month-by-month report.

   Accounting rules worth knowing:
   - **Credit card payments are excluded** — they appear in both files
     (checking debit, card credit) and card spending is already counted from
     the statement line items, so counting the payment would double-count.
   - **Savings transfers aren't spending** — the monthly transfer to savings is
     tracked separately from the spending categories.
   - **Refunds** post as negative amounts and reduce their category's month.

3. **`index.html`** — static dashboard reading `data.js`: KPI tiles (income,
   spending, net saved + savings rate), monthly spending stacked by category,
   ranked category totals, net cash flow by month, and a full category × month
   table. Hover any bar for details. Follows light/dark from your OS theme.

## Run it

```sh
python3 generate_mock_data.py   # regenerate the mock CSVs (seeded, reproducible)
python3 process.py              # categorize and rebuild summary.json + data.js
open index.html                 # or just double-click it
```

To point it at real data, export your bank/card CSVs into `data/` with the same
columns and extend the `RULES` list in `process.py` with your own merchants.
