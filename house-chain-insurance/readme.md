# House Chain Insurance

A model of how insurance could be baked into a chain of dependent property
sales — so that **flexible parties get paid for their flexibility**, and
**parties who need a specific timeline pay for it** instead of everyone
absorbing everyone else's risk for free.

Run it:

```
python3 model.py
```

No dependencies — Python 3.10+ stdlib only. There is also an in-browser
version of the simulator in [`index.html`](./index.html).

## The problem

In a chain, N households must complete on the same day. Two consequences:

1. **Completion date is a max, not an average.** The chain completes when
   the *slowest* party is ready, so expected delay grows with chain length
   even if every individual party is typically fast.
2. **Break risk compounds.** If each link independently falls through with
   probability p, the chain survives with probability (1−p)^N. At 8% per
   middle link, a 6-party chain breaks about a third of the time.

Everyone in the chain is exposed to these risks, but nobody prices them.
The party with a hard deadline (school start, expiring mortgage rate lock,
job relocation) silently bears enormous timing risk; the party with total
flexibility (no onward purchase, happy to rent for a while) provides real
option value to the whole chain and captures none of it.

The fix is standard financial engineering: make the risk transfer explicit
and let the natural hedger sell to the natural buyer.

## The four instruments

### A. Chain-break cover
Plain insurance: buyer pays a premium, insurer pays their sunk costs
(legal, survey, mortgage fees) if any link fails. Fair premium is just
`P(break) × sunk costs` plus loading. This exists in the real world
("home buyer protection insurance") and is the least interesting
instrument — it compensates loss but changes nobody's incentives.

### B. Delay option
The seller commits to a completion deadline **D** and pays liquidated
damages of £d per day past it (capped), voiding if the chain breaks. The
key result: the contract costs different sellers different amounts.

- An **inflexible** seller can only wait for the chain and pay whatever
  damages accrue.
- A **flexible** seller holds a hedge: if the chain drags, they can
  *bridge* — complete the sale on their own readiness and move into
  short-term accommodation until their onward purchase catches up. Their
  expected cost is `E[min(damages, bridge cost)]`, strictly less.

At a mid-market premium, the flexible seller books an expected profit and
the inflexible seller an expected loss on the identical contract.
**Flexibility is the hedge, and the premium is its yield.**

### C. Completion guarantee
The strong version: the seller guarantees completion by D *no matter what
happens upstream*. If the chain above them collapses, they bridge anyway
and the buyer still gets the house on time. Only a flexible party can
write this at a sane price — the inflexible party's "bridge cost" is
effectively infinite. This is the instrument a hard-deadline buyer
actually wants, and in the model it's a genuinely positive-sum trade: the
buyer's expected value exceeds the flexible seller's expected cost because
a collapsed chain costs the buyer far more (restarted search, lost rate
lock, temporary housing) than bridging costs the seller.

### D. Milestone bond pool
The symmetric, chain-wide mechanism — this is the "force parties to pay to
achieve specific timelines" piece. At the outset every party posts a bond
into escrow and commits to a common ready-by milestone. Each day a party
is late past the milestone they forfeit a fixed daily amount, split among
the parties who were ready; a party whose link fails forfeits the whole
bond. Effects:

- Being slow stops being free: it's a priced choice, paid to the people
  kept waiting.
- Fast, reliable parties earn a positive expected transfer — a yield on
  promptness — without any external insurer.
- Everyone gains an incentive to front-load their paperwork, which
  shortens the max and reduces break risk for the whole chain.

## Sample output

```
HOUSE CHAIN INSURANCE - MONTE CARLO PRICING REPORT
============================================================
chain: 6 parties, 50,000 simulations, seed 7
deadline D = 42 days; damages GBP 250/day capped at GBP 15,000

CHAIN RISK
  P(chain breaks)            =  32.4%
  completion | intact: median 42.2d, p90 61.4d, p99 83.5d
  P(late past deadline)      =  50.7% (given intact)
  buyer's uninsured expected cost = GBP 4,268

CHAIN LENGTH EFFECT (why long chains need this market)
  2 parties: P(break) =  5.9%   median completion =  21.3d   p90 =  35.5d
  3 parties: P(break) = 13.4%   median completion =  30.2d   p90 =  48.9d
  4 parties: P(break) = 20.4%   median completion =  35.5d   p90 =  55.5d
  5 parties: P(break) = 26.7%   median completion =  39.2d   p90 =  58.5d
  6 parties: P(break) = 32.6%   median completion =  42.4d   p90 =  61.6d
  7 parties: P(break) = 38.0%   median completion =  44.5d   p90 =  62.9d
  8 parties: P(break) = 42.9%   median completion =  46.6d   p90 =  65.7d

A. CHAIN-BREAK COVER (buyer buys from an insurer)
  fair premium   = GBP 1,297
  loaded premium = GBP 1,621

B. DELAY OPTION (seller commits to D, pays damages if late; voids on break)
  seller expected cost, unhedged        = GBP 1,515
  seller expected cost, hedged (bridge) = GBP 1,253
  buyer's raw deadline exposure         = GBP 1,518
  mid-market premium                    = GBP 1,384
  flexible seller expected profit       = GBP 131
  inflexible seller expected profit     = GBP -131

C. COMPLETION GUARANTEE (seller completes by D regardless of upstream)
  seller expected cost (bridging hedge) = GBP 3,111
  buyer expected value                  = GBP 4,089
  mid-market premium                    = GBP 3,600
  flexible seller expected profit       = GBP 489

D. MILESTONE BOND POOL (everyone posts GBP 5,000, forfeits GBP 100/day past day 35)
  expected net transfer by party:
    buyer      (mean ready 21.0d, p_fail   3%): GBP     +366
    mid_1      (mean ready 28.0d, p_fail   8%): GBP     -287
    mid_2      (mean ready 28.0d, p_fail   8%): GBP     -255
    mid_3      (mean ready 28.0d, p_fail   8%): GBP     -222
    mid_4      (mean ready 28.0d, p_fail   8%): GBP     -208
    top_seller (mean ready 14.0d, p_fail   3%): GBP     +605
```

## How the model works

- Each party's **days-to-ready** is gamma distributed (readiness is a
  series of roughly-exponential sequential tasks: searches, survey,
  mortgage offer, enquiries). Chain completion, given no break, is the
  max of the draws.
- Each party's link **fails** independently with probability `p_fail`;
  any failure breaks the chain.
- A seller's **flexibility** is two numbers: the fixed and daily cost of
  bridging (moving out and renting until they can re-buy). For an
  inflexible party, treat these as infinite.
- Instruments are priced by Monte Carlo expectation of their payoff legs;
  bilateral instruments (B, C) are quoted at the midpoint of seller cost
  and buyer value, splitting the surplus.

## Caveats, honestly

- **Perfect-foresight bridging.** The model lets the seller choose
  bridge-vs-damages knowing the realized delay, so the hedge value is an
  upper bound. A real seller decides under uncertainty at the deadline.
- **Moral hazard.** A party holding delay damages has weaker incentives to
  hurry; that's why instrument D (which prices *causing* delay, not
  suffering it) is the better chain-wide mechanism, and why real
  liquidated-damages clauses pair with milestone obligations.
- **Adverse selection.** Parties who know they're slow are keenest to buy
  timeline protection and least keen to post bonds. Mandatory,
  symmetric participation (D) at exchange sidesteps this.
- **Enforceability.** Pre-exchange commitments are hard to enforce in
  England & Wales precisely because nothing binds until exchange —
  which is also why the chain problem exists. Real-world adjacent
  products: reservation agreements with escrowed deposits, home buyer
  protection insurance, and US "buy-before-you-sell" bridge services,
  each implementing a slice of instruments A–D.
- Independence of link failures is optimistic (a falling market
  correlates them), and all money parameters are illustrative.
