#!/bin/sh

echo "Linting..."

((cargo --color=always test --all --all-features && \
cargo --color=always clippy -- -D warnings && \
cargo --color=always doc --workspace --all-features --no-deps --document-private-items) &>/tmp/lint.txt ) || (
    cat /tmp/lint.txt
    echo "YOU CAN'T COMMIT THIS GARBAGE!"
    exit 1
)
