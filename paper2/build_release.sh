#!/bin/sh
set -eu

cd "$(dirname "$0")"

# 2026-09-05 00:00:00 UTC. Callers may override this for a later release.
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1788566400}"
export FORCE_SOURCE_DATE=1
export TZ=UTC
export LC_ALL=C.UTF-8

latexmk -C fmm2.tex >/dev/null
latexmk -pdf -interaction=nonstopmode -halt-on-error fmm2.tex
