#!/bin/bash
find . -name '*.agda' | xargs -n1 -L1 agda
