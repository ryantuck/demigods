"""Monte Carlo pricing model for insurance instruments in housing chains.

A "chain" is a sequence of dependent property sales: the buyer at the bottom
can only complete when their seller completes their onward purchase, and so on
up to a chain-free seller at the top. Every party is exposed to the slowest
and flakiest link. This model prices four instruments that turn that shared
exposure into explicit, tradeable contracts:

  A. Chain-break cover      - insurance paying the buyer's sunk costs if any
                              link falls through.
  B. Delay option           - the seller commits to a completion deadline and
                              pays per-day liquidated damages past it; voids
                              if the chain breaks.
  C. Completion guarantee   - the seller commits to complete by the deadline
                              *no matter what happens upstream*, hedging by
                              bridging (moving to a rental) if needed.
  D. Milestone bond pool    - every party posts an escrowed bond and forfeits
                              a daily amount to the on-time parties for each
                              day they are late past a common milestone.

The central economic point: instruments B and C are naturally *written* by
flexible parties (cheap to bridge, no hard dates) and *bought* by constrained
parties (school start, rate-lock expiry, relocation). The spread between the
constrained party's expected uninsured cost and the flexible party's expected
hedged cost is the yield on flexibility. Instrument D is the symmetric
version: it forces whoever wants to be slow to pay the parties kept waiting.

All money figures are illustrative (GBP, since chains are most acute in
England & Wales). Run:  python3 model.py
"""

from __future__ import annotations

import random
import statistics
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# Chain definition
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Party:
    """One node in the chain.

    days-to-ready is gamma distributed: readiness requires several sequential
    tasks (searches, survey, mortgage offer, contract enquiries), each roughly
    exponential, so a gamma with integer-ish shape is a reasonable model.
    """

    name: str
    ready_shape: float   # gamma shape for days until ready to exchange
    ready_scale: float   # gamma scale (days); mean = shape * scale
    p_fail: float        # probability this party's link falls through

    def mean_ready(self) -> float:
        return self.ready_shape * self.ready_scale


def default_chain(n_parties: int = 6) -> list[Party]:
    """Position 0 is our buyer at the bottom; the last party is chain-free."""
    parties = [Party("buyer", ready_shape=4, ready_scale=5.25, p_fail=0.03)]
    for i in range(1, n_parties - 1):
        parties.append(
            Party(f"mid_{i}", ready_shape=4, ready_scale=7.0, p_fail=0.08)
        )
    parties.append(Party("top_seller", ready_shape=4, ready_scale=3.5, p_fail=0.03))
    return parties


@dataclass
class ChainDraw:
    broken: bool
    fail_index: int | None      # which party's link failed (None if intact)
    readies: list[float]        # days-to-ready per party (drawn regardless)
    completion: float | None    # max(readies) if intact, else None


def draw_chain(rng: random.Random, parties: list[Party]) -> ChainDraw:
    readies = [rng.gammavariate(p.ready_shape, p.ready_scale) for p in parties]
    for i, p in enumerate(parties):
        if rng.random() < p.p_fail:
            return ChainDraw(True, i, readies, None)
    return ChainDraw(False, None, readies, max(readies))


# ---------------------------------------------------------------------------
# Instrument terms
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Terms:
    deadline: float = 42.0        # committed completion day (6 weeks)
    damages_per_day: float = 250  # liquidated damages paid to the buyer
    damages_cap: float = 15_000
    sunk_costs: float = 4_000     # buyer's legal/survey/mortgage fees at risk
    break_disruption: float = 6_000   # buyer's further cost of a collapsed
                                      # chain: restarted search, lost rate
                                      # lock, months of temporary housing
    buyer_cost_per_day: float = 250   # buyer's real cost of each day late
    insurer_loading: float = 0.25     # margin over fair value for A
    # The option writer (our direct seller) can sever the chain by moving to
    # short-term accommodation instead of waiting for their own purchase.
    # These two numbers ARE the seller's flexibility: for an inflexible
    # party (kids in school, no fallback housing) treat them as infinite.
    bridge_fixed: float = 1_500       # removals, deposit, double overheads
    bridge_per_day: float = 60        # rent while waiting to re-buy
    rebuy_days: float = 90            # rental days if their purchase collapsed


def capped_damages(delay: float, t: Terms) -> float:
    return min(max(delay, 0.0) * t.damages_per_day, t.damages_cap)


# ---------------------------------------------------------------------------
# Instrument payoffs, evaluated on one chain draw
# ---------------------------------------------------------------------------

def buyer_uninsured_cost(d: ChainDraw, t: Terms) -> float:
    """What the constrained buyer expects to lose with no contract at all."""
    if d.broken:
        return t.sunk_costs + t.break_disruption
    return max(d.completion - t.deadline, 0.0) * t.buyer_cost_per_day


def delay_option_seller_cost(d: ChainDraw, t: Terms) -> float:
    """Instrument B, seller side. Voids on chain break (premium refunded, so
    the broken draws contribute zero to both legs).

    The seller (party 1) hedges by bridging: complete the sale on their own
    readiness, max(T_buyer, T_seller), and rent until their onward purchase
    is ready. We let them choose the cheaper of paying damages vs bridging
    with the realized draw - perfect foresight, so this is an upper bound on
    the hedge's value; an unhedged seller just pays the damages leg.
    """
    if d.broken:
        return 0.0
    pay_damages = capped_damages(d.completion - t.deadline, t)
    bridged_completion = max(d.readies[0], d.readies[1])
    bridge_cost = (
        t.bridge_fixed
        + t.bridge_per_day * max(d.completion - bridged_completion, 0.0)
        + capped_damages(bridged_completion - t.deadline, t)
    )
    return min(pay_damages, bridge_cost)


def guarantee_seller_cost(d: ChainDraw, t: Terms) -> float:
    """Instrument C, seller side: complete by the deadline no matter what.

    If the chain breaks anywhere above the seller, they bridge for
    `rebuy_days` while restarting their own purchase. Only a break at the
    buyer's own link (index 0) voids the deal.
    """
    if d.broken and d.fail_index == 0:
        return 0.0
    bridged_completion = max(d.readies[0], d.readies[1])
    late = capped_damages(bridged_completion - t.deadline, t)
    if d.broken:  # upstream break: forced bridge for the full re-buy period
        return t.bridge_fixed + t.bridge_per_day * t.rebuy_days + late
    if d.completion <= t.deadline:
        return 0.0
    pay_damages = capped_damages(d.completion - t.deadline, t)
    bridge_cost = (
        t.bridge_fixed
        + t.bridge_per_day * max(d.completion - bridged_completion, 0.0)
        + late
    )
    return min(pay_damages, bridge_cost)


def guarantee_buyer_residual(d: ChainDraw, t: Terms) -> float:
    """Buyer's remaining out-of-pocket cost under instrument C, before
    netting damages received. Late days are measured on the guaranteed
    (bridged) completion date."""
    if d.broken and d.fail_index == 0:
        # their own link failing is never insurable here
        return t.sunk_costs + t.break_disruption
    bridged_completion = max(d.readies[0], d.readies[1])
    if d.broken or d.completion > t.deadline:
        eff = bridged_completion if _would_bridge(d, t) else d.completion
    else:
        eff = d.completion
    late_days = max(eff - t.deadline, 0.0)
    return late_days * t.buyer_cost_per_day - capped_damages(late_days, t)


def _would_bridge(d: ChainDraw, t: Terms) -> bool:
    if d.broken:
        return True
    bridged_completion = max(d.readies[0], d.readies[1])
    pay = capped_damages(d.completion - t.deadline, t)
    bridge = (
        t.bridge_fixed
        + t.bridge_per_day * max(d.completion - bridged_completion, 0.0)
        + capped_damages(bridged_completion - t.deadline, t)
    )
    return bridge < pay


# ---------------------------------------------------------------------------
# Instrument D: milestone bond pool
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PoolTerms:
    milestone: float = 35.0       # common ready-by day everyone commits to
    forfeit_per_day: float = 100  # daily forfeit while late past milestone
    bond: float = 5_000           # escrowed cap on forfeits; whole bond is
                                  # forfeited by a party whose link fails


def pool_transfers(d: ChainDraw, parties: list[Party], pt: PoolTerms) -> list[float]:
    """Net transfer per party for one draw (positive = receives)."""
    n = len(parties)
    net = [0.0] * n
    forfeits = []
    for i in range(n):
        if d.broken and d.fail_index == i:
            forfeits.append((i, pt.bond))
        else:
            late = max(d.readies[i] - pt.milestone, 0.0)
            amount = min(late * pt.forfeit_per_day, pt.bond)
            if amount > 0:
                forfeits.append((i, amount))
    on_time = [i for i in range(n)
               if d.readies[i] <= pt.milestone
               and not (d.broken and d.fail_index == i)]
    for i, amount in forfeits:
        net[i] -= amount
        if on_time:
            share = amount / len(on_time)
            for j in on_time:
                net[j] += share
    return net


# ---------------------------------------------------------------------------
# Pricing report
# ---------------------------------------------------------------------------

def mean(xs: list[float]) -> float:
    return sum(xs) / len(xs) if xs else 0.0


def quantile(xs: list[float], q: float) -> float:
    if not xs:
        return 0.0
    s = sorted(xs)
    return s[min(int(q * len(s)), len(s) - 1)]


def run_report(n_parties: int = 6, n_sims: int = 50_000, seed: int = 7) -> str:
    rng = random.Random(seed)
    parties = default_chain(n_parties)
    t = Terms()
    pt = PoolTerms()

    draws = [draw_chain(rng, parties) for _ in range(n_sims)]
    intact = [d for d in draws if not d.broken]
    p_break = 1 - len(intact) / n_sims
    completions = [d.completion for d in intact]

    uninsured = [buyer_uninsured_cost(d, t) for d in draws]

    # A: chain-break cover
    fair_a = p_break * t.sunk_costs
    premium_a = fair_a * (1 + t.insurer_loading)

    # B: delay option (voids on break; condition both legs on intact chains)
    seller_cost_b = mean([delay_option_seller_cost(d, t) for d in intact])
    unhedged_cost_b = mean(
        [capped_damages(d.completion - t.deadline, t) for d in intact]
    )
    buyer_exposure_b = mean(
        [max(d.completion - t.deadline, 0) * t.buyer_cost_per_day for d in intact]
    )
    # The damages leg is worth exactly `unhedged_cost_b` in cash to the buyer,
    # so the tradeable spread is the flexibility edge (unhedged - hedged),
    # split 50/50 between writer and buyer.
    premium_b = (seller_cost_b + unhedged_cost_b) / 2

    # C: completion guarantee
    live = [d for d in draws if not (d.broken and d.fail_index == 0)]
    seller_cost_c = mean([guarantee_seller_cost(d, t) for d in live])
    buyer_value_c = mean(
        [buyer_uninsured_cost(d, t) - guarantee_buyer_residual(d, t) for d in live]
    )
    premium_c = (seller_cost_c + buyer_value_c) / 2

    # D: milestone bond pool
    nets = [pool_transfers(d, parties, pt) for d in draws]
    expected_net = [mean([n[i] for n in nets]) for i in range(n_parties)]

    # break probability vs chain length, same per-link params
    length_lines = []
    for n in range(2, 9):
        ps = default_chain(n)
        alive = 1.0
        for p in ps:
            alive *= 1 - p.p_fail
        ds = [draw_chain(rng, ps) for _ in range(10_000)]
        cs = [d.completion for d in ds if not d.broken]
        length_lines.append(
            f"  {n} parties: P(break) = {1 - alive:5.1%}   "
            f"median completion = {quantile(cs, 0.5):5.1f}d   "
            f"p90 = {quantile(cs, 0.9):5.1f}d"
        )

    lines = [
        "HOUSE CHAIN INSURANCE - MONTE CARLO PRICING REPORT",
        "=" * 60,
        f"chain: {n_parties} parties, {n_sims:,} simulations, seed {seed}",
        f"deadline D = {t.deadline:.0f} days; damages GBP {t.damages_per_day}/day "
        f"capped at GBP {t.damages_cap:,.0f}",
        "",
        "CHAIN RISK",
        f"  P(chain breaks)            = {p_break:6.1%}",
        f"  completion | intact: median {quantile(completions, 0.5):.1f}d, "
        f"p90 {quantile(completions, 0.9):.1f}d, "
        f"p99 {quantile(completions, 0.99):.1f}d",
        f"  P(late past deadline)      = "
        f"{mean([1.0 if c > t.deadline else 0.0 for c in completions]):6.1%} (given intact)",
        f"  buyer's uninsured expected cost = GBP {mean(uninsured):,.0f}",
        "",
        "CHAIN LENGTH EFFECT (why long chains need this market)",
        *length_lines,
        "",
        "A. CHAIN-BREAK COVER (buyer buys from an insurer)",
        f"  fair premium   = GBP {fair_a:,.0f}",
        f"  loaded premium = GBP {premium_a:,.0f}",
        "",
        "B. DELAY OPTION (seller commits to D, pays damages if late; voids on break)",
        f"  seller expected cost, unhedged        = GBP {unhedged_cost_b:,.0f}",
        f"  seller expected cost, hedged (bridge) = GBP {seller_cost_b:,.0f}",
        f"  buyer's raw deadline exposure         = GBP {buyer_exposure_b:,.0f}",
        f"  mid-market premium                    = GBP {premium_b:,.0f}",
        f"  flexible seller expected profit       = GBP {premium_b - seller_cost_b:,.0f}",
        f"  inflexible seller expected profit     = GBP {premium_b - unhedged_cost_b:,.0f}",
        "",
        "C. COMPLETION GUARANTEE (seller completes by D regardless of upstream)",
        f"  seller expected cost (bridging hedge) = GBP {seller_cost_c:,.0f}",
        f"  buyer expected value                  = GBP {buyer_value_c:,.0f}",
        f"  mid-market premium                    = GBP {premium_c:,.0f}",
        f"  flexible seller expected profit       = GBP {premium_c - seller_cost_c:,.0f}",
        "",
        "D. MILESTONE BOND POOL (everyone posts GBP "
        f"{pt.bond:,.0f}, forfeits GBP {pt.forfeit_per_day}/day past day "
        f"{pt.milestone:.0f})",
        "  expected net transfer by party:",
        *[
            f"    {parties[i].name:<10s} (mean ready {parties[i].mean_ready():4.1f}d, "
            f"p_fail {parties[i].p_fail:4.0%}): GBP {expected_net[i]:+8,.0f}"
            for i in range(n_parties)
        ],
        "",
        "READING THE RESULTS",
        "  - Flexibility is the hedge: the same delay-option premium that",
        "    roughly breaks even for an inflexible seller is mostly profit",
        "    for one who can cheaply bridge. Flexibility earns a yield.",
        "  - The guarantee premium is what a hard deadline actually costs;",
        "    a buyer who needs day-certain completion pays it, and a",
        "    flexible counterparty is the natural (profitable) writer.",
        "  - The bond pool makes slowness a priced choice: fast, reliable",
        "    parties collect from slow or flaky ones instead of subsidising",
        "    them with free waiting.",
    ]
    return "\n".join(lines)


if __name__ == "__main__":
    print(run_report())
