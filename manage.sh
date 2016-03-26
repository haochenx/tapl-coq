#!/bin/bash
set -e

VERSION="0.1.1"

CMD="$1"

function run_update {
    echo "update branch tapl-coq"
    (cd $(git rev-parse --show-toplevel); git subtree split --prefix garrigue/tapl-coq --branch tapl-coq)
}

function run_push {
    echo "pushing to github/tapl-coq"
    git push github/tapl-coq tapl-coq:master
}

case $CMD in
    update)
        run_update
        ;;
    push)
        run_push
        ;;
    magic)
        run_update && run_push
        ;;
    *)
        echo "usage: $0 update|push|magic" >&2
        echo "where magic = update && push" >&2
        exit 1
        ;;
esac
