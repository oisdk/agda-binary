#!/bin/bash
find . -name '*.agda' | xargs -n1 -L1 agda

recompile () {
    echo $1
    rm "$1.agdai"
    time agda "$1.agda"
}

recompile "Data/Binary/NonZero/Tests/Addition"
recompile "Data/Binary/Segmented/Tests/Addition"
recompile "Data/Binary/Distrib/Tests/Addition"
recompile "Data/Binary/NonZero/Tests/Multiplication"
recompile "Data/Binary/Segmented/Tests/Multiplication"
recompile "Data/Binary/Distrib/Tests/Multiplication"
