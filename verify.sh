#!/bin/bash

stack build
if [[ $# -eq 0 ]] ; then
    echo 'Verifying Model.hs...'
    stack exec -- liquid -i src src/Model.hs
    echo 'Verifying BinahLibrary.hs...'
    stack exec -- liquid --no-totality -i src --no-pattern-inline --prune-unsorted src/BinahLibrary.hs
    exit 0
fi
echo "Verifying $1..."
stack exec -- liquid -i src --no-pattern-inline --prune-unsorted $1
