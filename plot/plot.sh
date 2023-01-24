#!/usr/bin/env zsh

function plot {
    DOTFILE=$1
    NAME=$(basename $DOTFILE .dot)
    echo "I'm plotting: $NAME"
    dot2tex --autosize --template template $DOTFILE > $NAME.tex
    latexmk -xelatex $NAME.tex > /dev/null
    latexmk -c $NAME.tex > /dev/null
}

if [ -z $1 ]
then
    for DOTFILE in *.dot
    do
        plot $DOTFILE
    done
else
    plot $1
fi
