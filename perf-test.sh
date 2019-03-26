#!/bin/bash
echo "module Everything where" > Everything
find . -type f -name '*.agda' | while read -r file
do
    dots="$(echo "$file" | sed 's/\//\./g')"
    pref=${dots:2}
    modn="$(basename $pref '.agda')"
    echo "open import $modn" >> 'Everything'
done
mv Everything 'Everything.agda'
agda Everything.agda
rm Everything.agda

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
