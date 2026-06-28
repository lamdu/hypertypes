# Agent Instructions

When an AI coding agent contributes to a commit, include a co-author trailer for
that agent in the commit message.

Before committing Haskell changes, format with:

```sh
stack exec fourmolu -- --mode inplace src test Setup.hs
```
