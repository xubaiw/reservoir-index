#!/usr/bin/env bash
doc-gen4 /lean4_docs/ LeanDoc
rm -rf docs/
cp -r build/doc/ docs/
