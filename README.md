# Classifiying covering types in Cubical Agda

This repository contains the Cubical AGDA proof of the equivalence between subgroups of the fundamental groups and pointed connected coverings for a connected type $A$:

```math
\mathrm{Subgroup}(\pi_1(A)) \simeq \mathrm{Covering}(A),
```

as given in the paper _Classifying covering types in homotopy type theory_ by Samuel MIMRAM and Émile OLEON.
Small changes have been made so that this proof could be more Agda-friendly—primarily not working with explicit deloopings but rather with pointed connected groupoids.
A proof closer to the one implemented here can be found in the [internship report](https://hugos29.dev/data/ens1/stage-report.pdf) (pages 11–15).

**_This Agda-checked proof isn't fully complete yet!_**
But, very little is left to be proven (what remains is finishing one coherence-related proof: RightInv/Part2-Lemma).

Here is a breakdown of the proof and where it can be found in the file structure.

1. Transforming (the delooping of) a subgroup of $\pi_1(A)$ in a covering of $A$ ($\triangleright$ `SubgroupToCovering.agda`). This part has been fully checked by Agda.
2. Transforming a covering of $A$ in (the delooping of) a subgroup of $\pi_1(A)$ ($\triangleright$ `CoveringToSubgroup.agda`). This part has been fully checked by Agda.
3. Transforming from a subgroup to a covering back to a subgroups returns the original subgroup, up to homotopy ($\triangleright$ `LeftInv.agda` and `LeftInv/*.agda`). This part has been fully checked by Agda.
4. Transforming from a covering to a subgroup and back to a covering returns the same covering, up to homotopy ($\triangleright$ `RightInv.agda` and `RightInv/*.agda`).
   Agda has typechecked `RightInv/Part1.agda` and `RightInv/Part3.agda`, though the `RightInv/Part2.agda` is currenlty incomplete (hopefully, I'll have it fully written and typechecked soon).

Those files take a _really_ long time to compile.
The `check.py` file allows to compile files in parallel when they can.
You should expect a few hours of compiling (it took me around 3h30 to recompile everything with the script and 4h30 without it).
It's probably best to leave it compiling overnight.
