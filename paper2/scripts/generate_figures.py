#!/usr/bin/env python3
"""Verify exported examples and reproduce the paper's PNG figures and table.

Run from the package root: python3 scripts/generate_figures.py
Use --check-only for numerical checks without plotting dependencies.
"""
from pathlib import Path
from collections import deque
import argparse
import json
import math
import random

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'figures' / 'figure_data.json'


def price_time(claims, quantity):
    fills = []
    for claim in claims:
        fill = min(claim, quantity)
        fills.append(fill)
        quantity -= fill
    return fills


def replay(claims, lot, pointer, allowance, quantities):
    # Independent share-by-share specification, without Lean's fuel recursion.
    remaining = list(claims)
    order = deque(range(len(claims)))
    order.rotate(-pointer)
    records = []
    for quantity in quantities:
        fills = [0] * len(claims)
        for _ in range(min(quantity, sum(remaining))):
            while remaining[order[0]] == 0:
                order.rotate(-1)
            i = order[0]
            fills[i] += 1
            remaining[i] -= 1
            allowance -= 1
            if allowance == 0 or remaining[i] == 0:
                order.rotate(-1)
                allowance = lot
        records.append(fills)
    return records


def survivors(claims, lot, quantities, observations):
    return sum(replay(claims, lot, p, a, quantities) == observations
               for p in range(len(claims)) for a in range(1, lot + 1))


def labelled_fills(queue, quantity, ids):
    assert len({entry[1] for entry in queue}) == len(queue)
    assert set(ids) == {entry[1] for entry in queue} and len(ids) == len(queue)
    by_id = dict(zip((entry[1] for entry in queue),
                     price_time([entry[2] for entry in queue], quantity)))
    return [by_id[i] for i in ids]


def accepts_two(queue, quantity, ids, observed, delta):
    explanations = [queue]
    if abs(queue[0][0] - queue[1][0]) <= delta:
        explanations.append(queue[::-1])
    return any(labelled_fills(q, quantity, ids) == observed for q in explanations)


def verify(data):
    claims, lot, xs = data['claims'], data['lot'], data['quantities']
    obs = replay(claims, lot, 0, lot, xs)
    assert obs == data['observations']
    counts = [survivors(claims, lot, xs[:k], obs[:k]) for k in range(len(xs) + 1)]
    assert counts == data['survivors'] == [500, 1, 1, 1, 1, 1, 1]
    cyc = [data['full_cycle_quantity']]
    assert survivors(claims, lot, cyc, replay(claims, lot, 0, lot, cyc)) == data['full_cycle_survivors'] == 500
    assert data['depth_honest'] == price_time([200, 300], 400) == [200, 200]
    assert data['depth_jump'] == [100, 300]
    assert sum(data['depth_honest']) == sum(data['depth_jump']) == 400
    q = [(10, 1, 200), (12, 2, 200)]
    assert labelled_fills(q, 200, [1, 2]) == [200, 0]
    assert labelled_fills(q[::-1], 200, [1, 2]) == [0, 200]
    assert accepts_two(q, 200, [1, 2], [0, 200], 2) == data['clock_equal_size_accept'] is True
    assert accepts_two(q, 200, [1, 2], [0, 200], 1) == data['clock_equal_size_reject'] is False
    # Exercise both branches of the exact threshold with equal and unequal sizes,
    # partial and complete fills, and reversed external identifier order.
    cases = 0
    for qa in range(1, 5):
        for qb in range(1, 5):
            for quantity in range(qa + qb + 1):
                for gap in range(4):
                    queue = [(0, 7, qa), (gap, 9, qb)]
                    for ids in ([7, 9], [9, 7]):
                        first = labelled_fills(queue, quantity, ids)
                        swapped = labelled_fills(queue[::-1], quantity, ids)
                        if first == swapped:
                            continue
                        for delta in range(4):
                            assert accepts_two(queue, quantity, ids, swapped, delta) == (gap <= delta)
                            cases += 1
    print(f'Verified Lean figure data, finite phase filtering, and {cases} separating clock cases.')
    return cases


def simulation():
    rng = random.Random(7)
    n = 200_000
    gaps = [rng.expovariate(1.0) for _ in range(n)]
    rows = [{'lambda_delta': d,
             'masked_count': sum(g <= d for g in gaps),
             'analytic_probability': -math.expm1(-d)}
            for d in [0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0]]
    for row in rows:
        row['simulated_frequency'] = row['masked_count'] / n
    result = {'generator': 'Python random.Random / Mersenne Twister',
              'seed': 7, 'sample_size': n, 'distribution': 'exponential',
              'rate': 1.0, 'shared_sample': True, 'rows': rows}
    (ROOT / 'figures' / 'masking_data.json').write_text(json.dumps(result, indent=2) + '\n')
    (ROOT / 'tables').mkdir(exist_ok=True)
    lines = [f"{r['lambda_delta']:.2f} & {r['simulated_frequency']:.4f} & {r['analytic_probability']:.4f} " + r'\\' for r in rows]
    (ROOT / 'tables' / 'masking_rows.tex').write_text('\\newcommand{\\maskingrows}{%\n' + '\n'.join(lines) + '}\n')
    return rows


def plot(data, rows):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import PercentFormatter
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 11,
                         'axes.spines.top': False, 'axes.spines.right': False,
                         'axes.labelcolor': '#182c40', 'text.color': '#182c40',
                         'axes.titleweight': 'bold', 'savefig.facecolor': 'white'})
    blue, orange = '#1c587f', '#bf692a'
    def save(fig, name):
        fig.savefig(ROOT / 'figures' / name, dpi=450, bbox_inches='tight',
                    metadata={'Software': 'Matplotlib', 'Author': 'Miquel Noguer i Alonso'})
        plt.close(fig)

    fig, axes = plt.subplots(1, 2, figsize=(8.6, 3.15), layout='constrained')
    for k, (values, label, color) in enumerate([(data['depth_honest'], 'Price–time', blue),
                                               (data['depth_jump'], 'Priority transfer', orange)]):
        bars = axes[0].bar([k * .34, 1 + k * .34], values, width=.30, color=color, label=label)
        axes[0].bar_label(bars, padding=3)
    axes[0].set(xticks=[.17, 1.17], xticklabels=['Order A', 'Order B'], ylabel='Filled shares',
                ylim=(0, 355), title='Order-aligned depth')
    axes[0].legend(frameon=False, fontsize=9, loc='upper left')
    bars = axes[1].bar(['Price–time', 'Priority transfer'], [400, 400], color=[blue, orange], width=.55)
    axes[1].bar_label(bars, padding=3)
    axes[1].set(ylabel='Total printed shares', ylim=(0, 465), title='Total-only projection')
    save(fig, 'tape_depth_comparison.png')

    fig, axes = plt.subplots(1, 2, figsize=(8.6, 3.15), layout='constrained', gridspec_kw={'width_ratios': [1.6, 1]})
    counts = data['survivors']
    axes[0].plot(range(7), counts, marker='o', color=blue, linewidth=2)
    axes[0].set(yscale='log', xticks=range(7), yticks=[1, 5, 10, 100, 500],
                yticklabels=['1', '5', '10', '100', '500'], ylim=(.7, 1400),
                xlabel='Executions observed', ylabel='Surviving phase states (log scale)',
                title='Successive observations')
    axes[0].annotate('500', (0, 500), xytext=(7, 8), textcoords='offset points')
    axes[0].annotate('1 after the first execution', (1, 1), xytext=(10, 22), textcoords='offset points', fontsize=9)
    axes[0].grid(axis='y', alpha=.15)
    bars = axes[1].bar(['250 shares', '500 shares'], [1, data['full_cycle_survivors']], color=[blue, orange], width=.5)
    axes[1].bar_label(bars, padding=3)
    axes[1].set(yscale='log', ylim=(.7, 1400), yticks=[1, 10, 100, 500], yticklabels=['1', '10', '100', '500'], ylabel='Surviving phase states (log scale)', xlabel='First incoming quantity',
                title='Identification can fail')
    save(fig, 'latent_state_filter.png')

    fig, ax = plt.subplots(figsize=(7.8, 3.1), layout='constrained')
    xx = [j / 100 for j in range(251)]
    ax.plot(xx, [-math.expm1(-x) for x in xx], color=blue, linewidth=2.2, label=r'Analytic: $1-e^{-\lambda\delta}$')
    ax.scatter([r['lambda_delta'] for r in rows], [r['simulated_frequency'] for r in rows],
               marker='o', s=40, color=orange, edgecolors='white', linewidths=.6,
               zorder=3, label='Synthetic simulation')
    ax.set(xlabel=r'Uncertainty relative to arrival rate, $\lambda\delta$',
           ylabel='Masking probability', xlim=(0, 2.5), ylim=(0, 1))
    ax.yaxis.set_major_formatter(PercentFormatter(1))
    ax.grid(alpha=.15)
    ax.legend(frameon=False, loc='lower right')
    save(fig, 'clock_masking.png')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    data = json.loads(DATA.read_text())
    verify(data)
    if not args.check_only:
        plot(data, simulation())
        print('Generated three PNG figures and the probability table.')
