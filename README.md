# typical-antiphrasis

Here we collect and categorize logical paradoxes (proofs of falsum, *antinomies*) affecting variants of (Martin-Löf-style) type theory.

We aim to provide uniform, reasonably self-contained and didactically sound presentations of every known paradox, presented (when possible) as commented scripts in the language of the [Agda](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/what-is-agda.html) proof assistant.

We hope that the repository will serve as both a learning resource for those who wish to improve their understanding of logical paradoxes and their proofs in inconsistent type theories, as well as a reference for researchers in type theory who need to keep track of potential inconsistencies and *explosive* interactions between features.

## Usage

You can read the proofs and explanations as ordinary UTF-8 text files (e.g. via Github's built-in viewer). Type-checking the proofs requires a fairly recent version of Agda (2.6.0.1 should suffice) and [its standard library](https://github.com/agda/agda-stdlib/releases/tag/v1.3).

## Table of Contents

* [BuraliForti-Chains.agda](BuraliForti-Chains.agda): The straightforward version of the Burali-Forti paradox (the set of all well-ordered sets). Requires: `--type-in-type`, natural numbers.


## Contributing

1. Create a fork!
2. Create your feature branch: `git checkout -b my-new-feature`
3. Commit your changes: `git commit -am 'Add some feature'`
4. Push to the branch: `git push origin my-new-feature`
5. Submit a pull request.

Contributions that fix style issues/irregularities are welcome.
