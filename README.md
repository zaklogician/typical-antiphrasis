# typical-antiphrasis

Here we collect and categorize logical paradoxes (proofs of falsum, *antinomies*) affecting variants of (Martin-Löf-style) type theory.

We aim to provide uniform, reasonably self-contained and didactically sound presentations of every known paradox, presented (when possible) as commented scripts in the language of the [Agda](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/what-is-agda.html) proof assistant.

We hope that the repository will serve as both a learning resource for those who wish to improve their understanding of logical paradoxes and their proofs in inconsistent type theories, as well as a reference for researchers in type theory who need to keep track of potential inconsistencies and *explosive* interactions between features.

## Usage

You can read the proofs and explanations as ordinary UTF-8 text files (e.g. via Github's built-in viewer). Type-checking the proofs requires a fairly recent version of Agda (2.6.0.1 should suffice) and [its standard library](https://github.com/agda/agda-stdlib/releases/tag/v1.3).

## Table of Contents

* [BuraliForti-Chains.agda](BuraliForti-Chains.agda): The straightforward version of the Burali-Forti paradox (*does the set of all well-ordered sets admit a well-ordering?*) which defines descending chains explicitly using natural numbers. Requires: `--type-in-type`, sigma types, natural numbers.
* [Hypergame.agda](Hypergame.agda): The hypergame paradox (*is the game where you can choose to play any finite game itself finite?*; provenance unknown), which one may regard as a variant of the Burali-Forti paradox. Requires: `--type-in-type`, inductive types.
* [Liar.agda](Liar.agda): A version of the Liar paradox (*if I claim I'm lying, am I telling the truth?*) shows that the types of the constructors of an inductive data type may only occur strictly positively in the types of their arguments, on pain of inconsistency. Requires: `--no-positivity-check`, inductive types.
* [Russell-TypeIndexedSets.agda](Russell-TypeIndexedSets.agda): A version of Russell's paradox (*does the set of all sets that do not contain themselves contain itself?*) that uses (inductively defined) type-indexed sets to obtain an analogue of the set-theoretic membership relation. Requires: `--type-in-type`, inductive types.
* [Yablo.agda](Yablo.agda): Yablo's paradox (*if each Cretan asserts that all other Cretans are liars, is any one of them telling the truth?*) is a variant of the Liar paradox which demonstrates that positivity requirements cannot be relaxed even for parametrized (as opposed to indexed) types. Requires: `--no-positivity-check`, inductive types.

## Contributing

1. Create a fork!
2. Create your feature branch: `git checkout -b my-new-feature`
3. Commit your changes: `git commit -am 'Add some feature'`
4. Push to the branch: `git push origin my-new-feature`
5. Submit a pull request.

Contributions that fix style issues/irregularities are welcome.
