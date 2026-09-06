#!/usr/bin/env python3
"""Independent finite checks for the manuscript's examples and figure data.

Uses only the Python standard library. These checks supplement the Lean proofs;
they do not establish universal theorems or validate a production exchange.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def serial(q, x):
    a = []
    for r in q:
        g = min(r, x)
        a.append(g)
        x -= g
    return a


def wheel(q, x, lot, fuel=20):
    remaining = list(q)
    a = [0] * len(q)
    level = 0
    for _ in range(fuel):
        if x == 0:
            break
        for i, r in enumerate(remaining):
            g = min(lot, r, x)
            a[i] += g
            remaining[i] -= g
            x -= g
        if x == 0:
            break
        level += lot
    return a, x, level


@dataclass(frozen=True)
class State:
    records: tuple[tuple[int, int, int], ...]
    allowance: int


def init(q, lot, pointer=0):
    records = tuple((i, 0, r) for i, r in enumerate(q))
    return State(records[pointer:] + records[:pointer], lot)


def run(st, x, lot):
    records, allowance = list(st.records), st.allowance
    fuel = sum(r for _, _, r in records) + 1
    for _ in range(fuel):
        if x == 0 or not any(r for _, _, r in records):
            break
        while records[0][2] == 0:
            records = records[1:] + records[:1]
        i, a, r = records[0]
        g = min(allowance, r, x)
        head = (i, a + g, r - g)
        if g == min(allowance, r):
            records = records[1:] + [head]
            allowance = lot
        else:
            records[0] = head
            allowance -= g
        x -= g
    return State(tuple(records), allowance), x


def allocations(st, m):
    return [sum(a for j, a, _ in st.records if j == i) for i in range(m)]


def next_fills(st, x, lot, m):
    after = run(st, x, lot)[0]
    return [a-b for a, b in zip(allocations(after, m), allocations(st, m))]


def phase(m, lot, p, allowance):
    records = [(p, lot-allowance, lot+1+allowance)]
    records += [((p+k) % m, 0, 2*lot+1) for k in range(1, m)]
    return State(tuple(records), allowance)


def figure_data():
    q = [200, 300, 500]
    st = init([300, 300], 100)
    first = run(st, 100, 100)[0]
    partial = run(st, 150, 100)[0]
    final = run(partial, 150, 100)[0]
    pool = [300, 500, 0, 1000]
    a, _, w = wheel(pool, 1100, 100)
    prices = [99800, 99900, 100000, 100100, 100200, 100300]
    bids = [(100200,500), (100100,300), (100000,400), (99900,200)]
    asks = [(99800,300), (100000,300), (100100,400), (100300,500)]
    demand = [sum(n for v,n in bids if v >= p) for p in prices]
    supply = [sum(n for v,n in asks if v <= p) for p in prices]
    return {
        'comparison_claims': q,
        'comparison_serial': serial(q, 600),
        'comparison_parity': wheel(q, 600, 100)[0],
        'reset_combined': wheel([300,300],200,100)[0],
        'reset_split': [a+b for a,b in zip(wheel([300,300],100,100)[0],
                                           wheel([200,300],100,100)[0])],
        'persistent_combined': next_fills(st,200,100,2),
        'persistent_split': [a+b for a,b in zip(next_fills(st,100,100,2),
                                                next_fills(first,100,100,2))],
        'partial_fills': allocations(partial,2),
        'partial_pointer': partial.records[0][0],
        'partial_allowance': partial.allowance,
        'partial_final_fills': allocations(final,2),
        'partial_final_pointer': final.records[0][0],
        'partial_final_allowance': final.allowance,
        'partial_composition': run(st,300,100) == run(partial,150,100),
        'band_claims': pool, 'band_fills': a, 'band_level': w,
        'band_benchmark': [min(r,w) for r in pool],
        'pointer_probe_1': next_fills(phase(3,100,1,100),1,100,3),
        'pointer_probe_2': next_fills(phase(3,100,2,100),1,100,3),
        'allowance_probe_40': next_fills(phase(3,100,1,40),41,100,3),
        'allowance_probe_80': next_fills(phase(3,100,1,80),41,100,3),
        'allowance_curve_40': [next_fills(phase(3,100,1,40),x,100,3)[1] for x in range(101)],
        'allowance_curve_80': [next_fills(phase(3,100,1,80),x,100,3)[1] for x in range(101)],
        'auction_prices': prices, 'auction_demand': demand, 'auction_supply': supply,
        'auction_matched': [min(b,s) for b,s in zip(demand,supply)],
    }


def verify():
    expected = figure_data()
    actual = json.loads((ROOT/'figures/figure_data.json').read_text())
    require(actual == expected, 'Lean-exported figure data differs from independent calculation')
    require(expected['comparison_serial'] == [200,300,100], 'serial example')
    require(expected['comparison_parity'] == [200,200,200], 'parity example')
    require(expected['reset_split'] == [200,0], 'reset obstruction')
    require(expected['persistent_split'] == [100,100], 'persistent composition')
    require(expected['partial_composition'], 'partial-lot composition')
    require(expected['band_level'] == 300, 'explicit run-dependent level')
    require(expected['band_fills'] == [300,400,0,400], 'hybrid example')
    require(400*1800 < 1000*1100, 'book share example')
    require(serial([200,300,500,1000],1300) == [200,300,500,300], 'serial hybrid comparison')
    require(expected['allowance_probe_40'] == [0,40,1], '40-share allowance probe')
    require(expected['allowance_probe_80'] == [0,41,0], '80-share allowance probe')
    require(expected['auction_matched'][2:5] == [600,800,500], 'auction example')

    reachable, composition, band_checks, phase_pairs = 0, 0, 0, 0
    for m in range(1, 5):
        for q in product(range(4), repeat=m):
            for lot in range(1, 4):
                for p in sorted({0, m-1}):
                    st = init(q,lot,p)
                    for z in range(sum(q)+2):
                        reached,left = run(st,z,lot)
                        reachable += 1
                        a = allocations(reached,m)
                        require(sum(a)+left == z, 'reachable conservation')
                        require(all(0 <= a[i] <= q[i] for i in range(m)), 'reachable caps')
                        live = [(i,b,r) for i,b,r in reached.records if r]
                        if live:
                            require(reached.allowance == lot-live[0][1] % lot,
                                    'reachable allowance recovery')
                            require(all(b <= c+lot for _,b,_ in reached.records for _,c,_ in live),
                                    'persistent one-lot balance')
                        remaining = sum(q)-sum(a)
                        for x in range(remaining+1):
                            mid = run(reached,x,lot)[0]
                            for y in sorted({0,1,remaining+1}):
                                composition += 1
                                require(run(reached,x+y,lot) == run(mid,y,lot),
                                        'canonical state and leftover composition')
                    for x in range(sum(q)+2):
                        a,left,w = wheel(q,x,lot,sum(q)+1)
                        band_checks += 1
                        require(sum(a)+left == x, 'pass-wheel conservation')
                        require(sum(a) == min(x,sum(q)), 'pass-wheel completeness')
                        require(all(abs(v-min(r,w)) <= lot for v,r in zip(a,q)),
                                'explicit CEA bound')

    for m in range(2,6):
        for lot in range(1,7):
            phases = [(p,a) for p in range(m) for a in range(1,lot+1)]
            signatures = {}
            for p,a in phases:
                st = phase(m,lot,p,a)
                require(run(init([2*lot+1]*m,lot,p),lot-a,lot)[0] == st,
                        'phase family reachability')
                signature = tuple(tuple(next_fills(st,x,lot,m)) for x in range(1,lot+1))
                require(signature not in signatures, 'phase probe injectivity')
                signatures[signature] = (p,a)
            phase_pairs += len(phases)*(len(phases)-1)//2

    # Direct finite checks of the incompatibility and water-level identities.
    for lot in range(1,5):
        for x in range(lot+1,7):
            for w in range(8):
                require(not (x <= w+lot and 0 >= w), 'serial-band incompatibility')
    for q,s,t in product(range(12),repeat=3):
        require(min(q,s+t) == min(q,s)+min(q-min(q,s),t), 'water-level composition')
    require([a+b for a,b in zip(wheel([10,10],1,1)[0],
                                wheel([9,10],1,1)[0])] == [2,0], 'unit reset example')
    require(wheel([10,10],2,1)[0] == [1,1], 'unit combined example')
    require(1200*675 == 900**2, 'Tullock equilibrium example')
    require(Fraction(1200*300,975)-300 < Fraction(1200*225,900)-225, 'Tullock deviation')
    for n in range(1,25):
        def doubled(b,j):
            return (2*n if b>j else n if b==j else 0)-2*b
        values = [sum(doubled(b,j) for j in range(n+1)) for b in range(n+1)]
        require(values == [n-2*b for b in range(n+1)], 'uniform payoff formula')
        require(sum(values) == 0, 'uniform self-payoff')
        require(Fraction(max(values),2*(n+1)) < Fraction(1,2), 'uniform deviation bound')
    return {'figure_data_fields_checked':len(expected), 'reachable_runs_checked':reachable,
            'state_compositions_checked':composition, 'pass_wheel_bounds_checked':band_checks,
            'phase_pairs_separated':phase_pairs}


if __name__ == '__main__':
    print(json.dumps(verify(),indent=2))
