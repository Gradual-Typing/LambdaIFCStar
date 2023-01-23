#!/usr/bin/env zsh

for DOTFILE in *.dot
do
    NAME=$(basename $DOTFILE .dot)
    echo "I'm plotting: $NAME"
    dot2tex --autosize --template template $DOTFILE > $NAME.tex
    latexmk -xelatex $NAME.tex > /dev/null
    latexmk -c $NAME.tex > /dev/null
done
