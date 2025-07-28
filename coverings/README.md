# Classifiying covering types in Cubical Agda

This repository contains the Cubical AGDA proof of the equivalence between subgroups of the fundamental groups and pointed connected coverings for a connected type $A$:

```math
\mathrm{Subgroup}(\pi_1(A)) \simeq \mathrm{Covering}(A),
```

as given in the paper _Classifying covering types in homotopy type theory_ by Samuel MIMRAM and Émile OLEON.

**_This formal proof isn't fully complete yet !_**

Here is a breakdown of the proof and where it can be found in the file structure.

1. Transforming (the delooping of) a subgroup of $\pi_1(A)$ in a covering of $A$ ($\triangleright$ `SubgroupToCovering.agda`). This part has been fully checked by Agda.
2. Transforming a covering of $A$ in (the delooping of) a subgroup of $\pi_1(A)$ ($\triangleright$ `CoveringToSubgroup.agda`). This part has been fully checked by Agda.
3. Transforming from a subgroup to a covering back to a subgroups returns the original subgroup, up to homotopy ($\triangleright$ `LeftInv.agda` and `LeftInv/*.agda`).
   This part has been fully checked by Agda.
4. Transforming from a covering to a subgroup and back to a covering returns the same covering, up to homotopy ($\triangleright$ `RightInv.agda` and `RightInv/*.agda`).
   Agda has typechecked `RightInv/Part1.agda`, though the `RightInv/Part2.agda` is currenlty incomplete (hopefully, I'll have it fully written and typechecked soon).

Those files take a *really* long time to compile.
The `check.py` file allows to compile files in parallel when they can.
You should expect a few hours of compiling (at least, that's how long it took me).
It's probably best to leave it compiling overnight.
