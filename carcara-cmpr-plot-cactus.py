#!/usr/bin/env python3

from cmpr import prepare_data
from cmpr import KEY_CONFIG, KEY_BENCHMARK, KEY_TIME_CPU, KEY_TIME_REAL, KEY_SOLVED

import argparse
import statistics
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as pyplot
import pandas

COLOR_DEFAULT = 'black'
COLOR_FAST10 = 'C1'
COLOR_FAST100 = 'C3'
COLOR_SLOW10 = 'C0'
COLOR_SLOW100 = 'darkblue'


def die(msg):
    print('error: {}'.format(msg))
    sys.exit(1)


def plot(df, column):
    df = df.reset_index()

    timeout = args.time_limit if args.time_limit else df[column].max()
    df = df.loc[(df["valid"] > 0) & (df[column] < timeout)]
    # Rank by number of solved
    ranking = df.groupby(KEY_CONFIG, as_index=False).agg({
        "valid": 'sum'
    }).sort_values(by="valid", ascending=False)
    configs = ranking[KEY_CONFIG].unique()

    marker = ['o', 'v', '^', 's', 'p', '*', '+', 'x', 'D', 'd']
    colors = [
        '#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd', '#8c564b',
        '#e377c2', '#7f7f7f', '#bcbd22', '#17becf'
    ]

    matplotlib.rc('text', usetex=True)
    font = {'size': 14, 'monospace': 'Computer Modern Typewriter'}
    matplotlib.rc('font', **font)

    fig, ax = pyplot.subplots()

    j = 0
    for config in configs:
        data = df.loc[df[KEY_CONFIG] == config,
                      [column]].sort_values(by=[column])
        # Print solved instances with marker
        x = [i + 1 for i in range(0, len(data))]
        y = data
        x_unsolved = [x[-1], x[-1]]
        y_unsovled = [list(y[column])[-1], timeout * 1.025]

        if args.cdf:
            x, y = y, x
            x_unsolved, y_unsovled = y_unsovled, x_unsolved
        ax.plot(x,
                y,
                color=colors[j],
                linewidth=1,
                marker=marker[j],
                markersize=3,
                label=config.replace('_', '\\_'))
        # Print timeout line
        ax.plot(x_unsolved, y_unsovled, color=colors[j], linewidth=1)
        j = (j + 1) % len(marker)

    if args.cdf:
        ax.axvline(x=timeout,
                   color='darkgray',
                   linestyle='dotted',
                   linewidth=1)
        ax.set_ylim(ymin=0)
        ax.set_xlim(xmin=0, xmax=timeout * 1.025)
        xlabel = args.ylabel
        ylabel = args.xlabel
        loc = 'lower right'
    else:
        ax.axhline(y=timeout,
                   color='darkgray',
                   linestyle='dotted',
                   linewidth=1)
        if args.xmax:
          ax.set_xlim(xmin=args.xmin, xmax=args.xmax)
        else:
          ax.set_xlim(xmin=args.xmin)
        ax.set_ylim(ymin=args.ymin, ymax=timeout * 1.025)
        xlabel = args.xlabel
        ylabel = args.ylabel
        loc = 'upper left'

    pyplot.xlabel('\\textbf{{{}}}'.format(xlabel))
    pyplot.ylabel('\\textbf{{{}}}'.format(ylabel))
    ax.grid(color='lightgray')
    ax.legend(loc=loc, fontsize='x-small')


    logFormatter = pyplot.LogFormatterMathtext(base=10)
    # ax.xaxis.set_major_formatter(logFormatter)
    ax.yaxis.set_major_formatter(logFormatter)

    fig.savefig('cactus_plot.png', bbox_inches='tight')
    print('Saved to cactus_plot.png')

    if args.eps:
        fig.savefig('cactus_plot.eps', bbox_inches='tight')
        print('Saved to cactus_plot.eps')


if __name__ == '__main__':

    ap = argparse.ArgumentParser()
    ap.add_argument('--xmin',
                    type=int,
                    default=0,
                    help='Start of x axis')
    ap.add_argument('--xmax',
                    type=int,
                    default=0,
                    help='End of x axis')
    ap.add_argument('--ymin',
                    type=float,
                    default=0,
                    help='Start of y axis')
    ap.add_argument('--xlabel',
                    type=str,
                    default='solved instances',
                    help='Plot label for x axis')
    ap.add_argument('--ylabel',
                    type=str,
                    default='runtime [s]',
                    help='Plot label for y axis')
    ap.add_argument('--eps',
                    action='store_true',
                    default=False,
                    help='Generate EPS file')
    ap.add_argument('--time-limit', type=int, help='Maximum time limit')
    ap.add_argument('--wall',
                    action='store_true',
                    help='Use wall-clock time instead of CPU time')
    ap.add_argument('--cdf', action='store_true', help='Flip x and y axis')
    args, cmpr_args = ap.parse_known_args()

    df = prepare_data(cmpr_args)
    plot(df, KEY_TIME_REAL if args.wall else KEY_TIME_CPU)
