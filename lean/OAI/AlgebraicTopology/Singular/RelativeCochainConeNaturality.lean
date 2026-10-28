/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Singular.RelativeCochainG
import OAI.Algebra.Homology.LinearDualNaturality
import OAI.Algebra.Homology.DerivedCategoryConeNaturality

/-! # Relative Cochain Cone Naturality -/

namespace OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality

noncomputable section

/-! # Canonical natural relative-cochain cone comparison

The explicit short-exact-sequence lift is natural already before passage to homology.

The lift is positive `(inclusion, 0)`; Mathlib's cone connecting morphism is the negative first
projection. Their composite is displayed below.

Agreement with `relativeCochainConeCohomologyEquiv`, which is built from a completed triangle map,
is a separate comparison theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R]

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
identifies `H^n(C^*(X, A; R))` with `H^{n-1}(Cone(C^*(X; R) → C^*(A; R)))`. The complexes are
extended by zero to integer degrees before taking the cone. The comparison uses the map with
components `(inclusion, 0)`, fixing its sign. -/
def relativeDualCochainHomologyIsoCone (X : TopPair.{u}) (n : ℕ) :
    (RelativeCochainCone.relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≅
      (CochainComplex.mappingCone (RelativeCochainCone.relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) :=
  Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone
    (RelativeCochainCone.relativeDualCochainShortComplexInt R X)
    (RelativeCochainG.relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) n (by omega)

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`.
Extending the relative cochain complex by zero to negative integer degrees leaves its degree-`n`
cohomology unchanged. This is the resulting linear equivalence with relative singular cohomology
`H^n(X, A; R)`. -/
def relativeDualCochainCohomologyEquiv (X : TopPair.{u}) (n : ℕ) :
    (RelativeCochainCone.relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≃ₗ[R]
      Cohomology.RelativeCohomology R X n :=
  ((Cohomology.RelativeCochainComplex R X).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).toLinearEquiv

/-- Let `R` be a commutative ring and `(X, A)` a topological pair, with `A` embedded in `X`. This
linear equivalence identifies `H^{n-1}(Cone(C^*(X; R) → C^*(A; R)))` with relative singular
cohomology `H^n(X, A; R)`. It is inverse to the cohomology map induced by the relative-cochain
inclusion with zero second cone component. -/
def relativeCochainConeCohomologyEquivCanonical (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (RelativeCochainCone.relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≃ₗ[R] Cohomology.RelativeCohomology R X n :=
  (relativeDualCochainHomologyIsoCone R X n).symm.toLinearEquiv.trans
    (relativeDualCochainCohomologyEquiv R X n)

end

end OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality
