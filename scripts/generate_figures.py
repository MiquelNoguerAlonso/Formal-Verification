#!/usr/bin/env python3
"""Render the paper's five PNG figures from checked Lean-exported quantities."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from numerical_review import figure_data, require

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'figures'
D = json.loads((OUT/'figure_data.json').read_text())
require(D == figure_data(), 'Figure data must match the independent calculation')
BLUE, TEAL, ORANGE = '#245A81', '#168477', '#C77C21'
INK, GREY, LIGHT = '#243442', '#647584', '#E8EDF1'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10.5,
    'axes.labelsize':10,'axes.titlesize':11,'axes.titleweight':'bold',
    'text.color':INK,'axes.labelcolor':INK,'xtick.color':INK,'ytick.color':INK,
    'axes.edgecolor':GREY,'axes.spines.top':False,'axes.spines.right':False,
    'axes.linewidth':0.7,'grid.color':'#DAE1E6','grid.linewidth':0.6,
    'savefig.facecolor':'white','figure.facecolor':'white',
    'mathtext.fontset':'dejavusans'})


def save(fig,name):
    fig.savefig(OUT/name,dpi=450,bbox_inches='tight',pad_inches=0.08,
                metadata={'Software':'Matplotlib; scripts/generate_figures.py'})
    plt.close(fig)


def comparison():
    fig,axes=plt.subplots(1,2,figsize=(7.0,2.9),sharex=True,sharey=True)
    for ax,key,title,color in zip(axes,['comparison_serial','comparison_parity'],
                                  ['(a) Price-time','(b) Parity, lot = 100'],[BLUE,TEAL]):
        for i,(q,a) in enumerate(zip(D['comparison_claims'],D[key])):
            ax.barh(i,q,color=LIGHT,height=.55,edgecolor='white')
            ax.barh(i,a,color=color,height=.55)
            ax.text(a/2,i,str(a),color='white',ha='center',va='center',fontsize=10)
            ax.text(q+9,i,f'claim {q}',ha='left',va='center',fontsize=9,color=GREY)
        ax.set_yticks([0,1,2],['Participant 1','Participant 2','Participant 3'])
        ax.set_xlim(0,660)
        ax.set_xticks([0,200,400,600])
        ax.set_xlabel('Shares')
        ax.set_title(title,loc='left',pad=12)
        ax.set_axisbelow(True);ax.grid(axis='x',alpha=.7)
        ax.spines['left'].set_visible(False);ax.tick_params(axis='y',length=0)
    axes[0].invert_yaxis()
    axes[1].tick_params(labelleft=False)
    fig.subplots_adjust(left=.17,right=.98,bottom=.26,top=.83,wspace=.15)
    fig.legend(handles=[Patch(facecolor=GREY,label='Filled (numbers inside bars)'),
                        Patch(facecolor=LIGHT,label='Unfilled capacity')],
               loc='lower center',ncol=2,frameon=False,fontsize=9)
    save(fig,'allocation_comparison.png')


def composition():
    fig,ax=plt.subplots(figsize=(7.0,3.45))
    rows=[('Reset: one order of 200',D['reset_combined']),
          ('Reset: orders of 100 + 100',D['reset_split']),
          ('Persistent: either segmentation',D['persistent_split'])]
    for y,(label,fills) in enumerate(rows):
        start=0
        for participant,n in enumerate(fills):
            if n:
                ax.barh(y,n,left=start,height=.48,color=[BLUE,TEAL][participant])
                ax.text(start+n/2,y,f'{["A","B"][participant]}: {n}',ha='center',va='center',color='white')
                start+=n
        ax.text(207,y,f'({fills[0]}, {fills[1]})',ha='left',va='center',fontsize=10)
    ax.set_yticks(range(3),[label for label,_ in rows],fontsize=9.5)
    ax.set_ylim(2.55,-.6);ax.set_xlim(0,255)
    ax.set_xticks([0,100,200]);ax.set_xlabel('Cumulative incoming shares')
    ax.axvline(100,color=INK,ls=(0,(3,3)),lw=.9)
    ax.tick_params(axis='y',length=0);ax.spines['left'].set_visible(False)
    ax.set_title('Same initial claims (300, 300), lot = 100, initial pointer A',loc='left',fontsize=10.5,pad=12)
    fig.subplots_adjust(left=.36,right=.98,top=.85,bottom=.34)
    fig.text(.08,.105,'Partial-lot example: after 150 shares, fills = (100, 50), pointer B, allowance 50.',fontsize=9.5)
    fig.text(.08,.035,'Another 150 gives (200, 100), pointer B, allowance 100: the same state as 300 at once.',fontsize=9.2)
    save(fig,'stream_composition.png')


def band():
    fig,ax=plt.subplots(figsize=(7.0,2.95))
    x=list(range(4));base=D['band_benchmark']
    delta=[a-b for a,b in zip(D['band_fills'],base)]
    ax.bar(x,base,.56,color=BLUE,label='Benchmark at computed level w = 300')
    ax.bar(x,delta,.56,bottom=base,color=ORANGE,hatch='///',edgecolor='white',
           linewidth=.5,label='Wheel fill above this benchmark')
    for i,a in enumerate(D['band_fills']):
        ax.text(i,a+13,str(a),ha='center',va='bottom',fontsize=10)
    ax.axhline(300,color=GREY,lw=.9,ls='--',zorder=0)
    ax.set_ylim(0,475);ax.set_xlim(-.6,3.6)
    ax.set_xticks(x,['Market maker','Broker 1','Broker 2\n(setter removed)','Electronic book'],fontsize=9)
    ax.set_yticks([0,100,200,300,400]);ax.set_ylabel('Parity-pool fills (shares)')
    ax.set_title('Explicit wheel level for the hybrid worked example',loc='left',pad=11)
    ax.grid(axis='y',alpha=.65);ax.set_axisbelow(True)
    fig.subplots_adjust(left=.12,right=.98,top=.85,bottom=.34)
    fig.legend(loc='lower center',ncol=1,frameon=False,fontsize=9,bbox_to_anchor=(.52,-.025))
    save(fig,'wheel_water_level.png')


def auction():
    fig,axes=plt.subplots(1,2,figsize=(7.0,3.25),gridspec_kw={'width_ratios':[1.25,1]})
    ax=axes[0];p=[x/10000 for x in D['auction_prices']]
    ax.step(p,D['auction_demand'],where='pre',label='Demand',color=BLUE,lw=2)
    ax.step(p,D['auction_supply'],where='post',label='Supply',color=TEAL,lw=2,ls='--')
    ax.scatter([10.01]*2,[800,1000],s=32,c=[BLUE,TEAL],zorder=5)
    ax.vlines(10.01,800,1000,color=ORANGE,lw=4,zorder=4)
    ax.annotate('200-share\nsell imbalance',xy=(10.01,900),xytext=(9.979,1070),
                arrowprops={'arrowstyle':'->','color':GREY},fontsize=9)
    ax.set_xlim(9.977,10.033);ax.set_ylim(0,1650)
    ax.set_xticks([9.98,10.00,10.02]);ax.set_xticklabels(['9.98','10.00','10.02'])
    ax.set_xlabel('Candidate price ($)');ax.set_ylabel('Eligible shares')
    ax.set_title('(a) Demand and supply',loc='left',pad=12)
    ax.legend(frameon=False,loc='upper left',fontsize=9,ncol=2)
    ax.grid(axis='y',alpha=.6);ax.set_axisbelow(True)
    ax=axes[1]
    matched=D['auction_matched'][2:5]
    ax.bar([0,1,2],matched,.58,color=[LIGHT,TEAL,LIGHT],edgecolor=[GREY,TEAL,GREY])
    for i,n in enumerate(matched):ax.text(i,n+22,str(n),ha='center',fontsize=10)
    ax.set_xticks([0,1,2],['10.00','10.01','10.02']);ax.set_xlabel('Candidate price ($)')
    ax.set_ylabel('Matched shares');ax.set_ylim(0,1050)
    ax.set_title('(b) Matched volume',loc='left',pad=12)
    ax.grid(axis='y',alpha=.6);ax.set_axisbelow(True)
    fig.subplots_adjust(left=.1,right=.98,bottom=.20,top=.85,wspace=.39)
    save(fig,'auction_price_selection.png')


def probes():
    fig,axes=plt.subplots(1,2,figsize=(7.0,3.65),gridspec_kw={'width_ratios':[1,1.15]})
    ax=axes[0]
    for y,key in enumerate(['pointer_probe_1','pointer_probe_2']):
        for i,n in enumerate(D[key]):
            ax.text(i,y,str(n),ha='center',va='center',fontsize=14,fontweight='bold',
                    color='white' if n else GREY,
                    bbox={'boxstyle':'round,pad=.4','facecolor':BLUE if n else LIGHT,'edgecolor':'none'})
    ax.set_xlim(-.6,2.6);ax.set_ylim(1.6,-.6)
    ax.set_yticks([0,1],[r'$P_{1,100}$',r'$P_{2,100}$'])
    ax.set_xticks([0,1,2],['Label 0','Label 1','Label 2'],fontsize=9)
    ax.set_xlabel('New fills from one share')
    ax.set_title('(a) The first share identifies p',loc='left',pad=13,fontsize=10.5)
    ax.tick_params(length=0)
    for spine in ax.spines.values():spine.set_visible(False)
    ax=axes[1]
    ax.step(range(101),D['allowance_curve_40'],where='post',color=BLUE,lw=2,label='Allowance 40')
    ax.step(range(101),D['allowance_curve_80'],where='post',color=ORANGE,lw=2,ls='--',label='Allowance 80')
    ax.axvline(41,color=GREY,lw=.8,ls=':')
    ax.annotate('At x = 41:\n40 versus 41',xy=(41,40),xytext=(3,68),fontsize=9,
                arrowprops={'arrowstyle':'->','color':GREY})
    ax.set_xlim(0,100);ax.set_ylim(0,105);ax.set_xticks([0,40,80,100]);ax.set_yticks([0,40,80,100])
    ax.set_xlabel('Incoming estate x (shares)');ax.set_ylabel('New fill to label 1')
    ax.set_title('(b) A boundary probe identifies a',loc='left',pad=13,fontsize=10.5)
    ax.legend(loc='lower right',frameon=False,fontsize=8.5)
    ax.grid(alpha=.55);ax.set_axisbelow(True)
    fig.subplots_adjust(left=.11,right=.98,bottom=.33,top=.84,wspace=.46)
    fig.text(.10,.115,'Left: identical zero cumulative fills. Right: cumulative fills at label 1 are 60 and 20.',fontsize=9)
    fig.text(.10,.035,r'If cumulative fills are supplied, the reachable-state identity recovers $a=100-(A_p\,\mathrm{mod}\,100)$.',fontsize=9.3)
    save(fig,'future_state_probes.png')


if __name__ == '__main__':
    for draw in [comparison,composition,band,auction,probes]:draw()
    print('Rendered five PNG figures at 450 dpi from checked numerical data.')
