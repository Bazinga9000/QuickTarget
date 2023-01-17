#!/bin/sh
set -e
TARGETED=Targeted

# Extract and compile the example
coqc -Q ../../src QuickChick ${TARGETED}.v
