#!/usr/bin/env python3

from cmpr import prepare_data
from cmpr import KEY_CONFIG, KEY_BENCHMARK, KEY_TIME_CPU, KEY_TIME_REAL

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


def plot(df, column, dirs):
    df = df.reset_index()
    configs = df[KEY_CONFIG].unique()

    if len(configs) != 2:
        die('Scatter plot expects exactly two runs')

    config_x = configs[0]
    config_y = configs[1]

    # Make sure that the order of configurations is correct
    if config_x in dirs[1]:
        config_x, config_y = config_y, config_x

    if args.time_limit:
        timeout = args.time_limit
    else:
        timeout = df[column].max()

    time_x = df.loc[df[KEY_CONFIG] == config_x, [KEY_BENCHMARK, column]]
    time_y = df.loc[df[KEY_CONFIG] == config_y, [KEY_BENCHMARK, column]]

    ddf = pandas.merge(time_x, time_y, on=KEY_BENCHMARK)
    ddf.columns = [KEY_BENCHMARK, config_x, config_y]

    matplotlib.rc('text', usetex=True)
    font = {'size': 14, 'monospace': 'Computer Modern Typewriter'}
    matplotlib.rc('font', **font)
    fig, ax = pyplot.subplots(figsize=(5, 5))

    ax.set_xscale('log')
    ax.set_yscale('log')

    min_val = 1 / 10
    max_val = timeout * 1.15

    X = [0]
    cur_x = min_val
    while cur_x < max_val:
        X.append(cur_x)
        cur_x = cur_x * 10
    X.append(max_val)

    ax.plot(X, X, color='darkgray', linestyle='dotted', linewidth=1)
    if args.fast10:
        ax.plot(X, [x / 10 for x in X],
                color=COLOR_FAST10,
                linestyle='dashed',
                linewidth=1)
    if args.fast100:
        ax.plot(X, [x / 100 for x in X],
                color=COLOR_FAST100,
                linestyle='dashed',
                linewidth=1)
    if args.slow10:
        ax.plot(X, [x * 10 for x in X],
                color=COLOR_SLOW10,
                linestyle='dashed',
                linewidth=1)
    if args.slow100:
        ax.plot(X, [x * 100 for x in X],
                color=COLOR_SLOW100,
                linestyle='dashed',
                linewidth=1)

    ax.axhline(y=timeout, color='darkgray', linestyle='dashed', linewidth=1)
    ax.axvline(x=timeout, color='darkgray', linestyle='dashed', linewidth=1)

    colors = []
    x_values = ddf[config_x]
    y_values = ddf[config_y]
    faster_10x = 0
    faster_100x = 0
    slower_10x = 0
    slower_100x = 0

    for i in range(len(x_values)):
        xval = x_values[i]
        yval = y_values[i]

        color = COLOR_DEFAULT
        speedup = xval / yval if yval > 0 else 0
        slowdown = yval / xval if xval > 0 else 0

        if speedup >= 100:
            color = COLOR_FAST100
            faster_100x += 1
        elif speedup >= 10:
            color = COLOR_FAST10
            faster_10x += 1
        elif slowdown >= 100:
            color = COLOR_SLOW100
            slower_100x += 1
        elif slowdown >= 10:
            color = COLOR_SLOW10
            slower_10x += 1

        colors.append(color)

    ax.scatter(x_values,
               y_values,
               s=16,
               marker='.',
               c=colors,
               alpha=0.8,
               edgecolors='face')

    # Generate legend
    legend_elements = []
    if faster_10x > 0 and args.fast10:
        legend_elements.append(
            pyplot.Line2D([], [],
                          marker='.',
                          label='10x faster ({})'.format(faster_10x),
                          color=COLOR_FAST10))
    if faster_100x > 0 and args.fast100:
        legend_elements.append(
            pyplot.Line2D([], [],
                          marker='.',
                          label='100x faster ({})'.format(faster_100x),
                          color=COLOR_FAST100))

    if slower_10x > 0 and args.slow10:
        legend_elements.append(
                pyplot.Line2D([], [], marker='.',
                              label='10x slower ({})'.format(slower_10x),
                              color=COLOR_SLOW10))
    if slower_100x > 0 and args.slow100:
        legend_elements.append(
                pyplot.Line2D([], [], marker='.',
                              label='100x slower ({})'.format(slower_100x),
                              color=COLOR_SLOW100))

    ax.legend(handles=legend_elements, loc='upper left')
    ax.set_ylim(min_val / 1.2, max_val)
    ax.set_xlim(min_val / 1.2, max_val)
    ax.set_aspect('equal')

    ticks = X[1:-1]
    ticks_labels = [str(x) for x in ticks]
    pyplot.xticks(ticks, labels=ticks_labels)
    pyplot.yticks(ticks, labels=ticks_labels)

    if not args.xlabel:
        args.xlabel = config_x
    if not args.ylabel:
        args.ylabel = config_y

    pyplot.xlabel('\\textbf{{{}}} runtime [s]'.format(
        args.xlabel.replace('_', '\\_')))
    pyplot.ylabel('\\textbf{{{}}} runtime [s]'.format(
        args.ylabel.replace('_', '\\_')))
    fig.savefig('scatter_plot.png', bbox_inches='tight')
    print('Saved to scatter_plot.png')

    if args.eps:
        fig.savefig('scatter_plot.eps', bbox_inches='tight')
        print('Saved to scatter_plot.eps')

if __name__ == '__main__':

    ap = argparse.ArgumentParser()
    ap.add_argument('--xlabel', type=str, help='Plot label for x axis')
    ap.add_argument('--ylabel', type=str, help='Plot label for y axis')
    ap.add_argument('--eps',
                    action='store_true',
                    default=False,
                    help='Generate EPS file')
    ap.add_argument('--time-limit', type=int, help='Maximum time limit')
    ap.add_argument('--wall',
                    action='store_true',
                    help='Use wall-clock time instead of CPU time')
    ap.add_argument('--fast10',
                    action='store_true',
                    default=True)
    ap.add_argument('--fast100',
                    action='store_true',
                    default=True)
    ap.add_argument('--slow10',
                    action='store_true',
                    default=True)
    ap.add_argument('--slow100',
                    action='store_true',
                    default=True)
    args, cmpr_args = ap.parse_known_args()

    dirs = []
    for arg in cmpr_args:
        if arg[0] != '-':
            dirs.append(arg)
    df = prepare_data(cmpr_args)
    plot(df, KEY_TIME_REAL if args.wall else KEY_TIME_CPU, dirs)
