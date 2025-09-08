open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Base

import SubgroupToCovering
import CoveringToSubgroup
import LeftInv
import RightInv

module Correspondance (A : Pointed ℓ-zero) where
  galoisCorrespondanceIso : Iso (SubGroupπ₁ A) (Covering A)
  galoisCorrespondanceIso .Iso.fun = SubgroupToCovering.coveringA A
  galoisCorrespondanceIso .Iso.inv = CoveringToSubgroup.subgrp A
  galoisCorrespondanceIso .Iso.rightInv = RightInv.rightInv A
  galoisCorrespondanceIso .Iso.leftInv = LeftInv.leftInv A

  galoisCorrespondance : SubGroupπ₁ A ≃ Covering A
  galoisCorrespondance = isoToEquiv galoisCorrespondanceIso
