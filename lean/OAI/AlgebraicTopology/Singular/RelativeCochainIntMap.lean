/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Singular.RelativeCochainConeNaturality

/-! # Relative Cochain Int Map -/

namespace OAI.AlgebraicTopology.Singular.RelativeCochainIntMap

noncomputable section

/-!
# Canonical natural relative-cochain cone comparison

-/

/-! ### Constructions used only in proofs -/

section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `R` be a commutative ring and `f: (X,A) → (Y,B)` a continuous map of topological pairs.
Pullback of singular cochains gives this map from the sequence `C^•(Y,B;R) → C^•(Y;R) →
C^•(B;R)` to the corresponding sequence for `(X,A)`. Relative cochains are the `R`-linear duals
of the quotient chain complexes, and the complexes are indexed by nonnegative integers. -/
def relativeDualCochainShortComplexNatMap {X Y : TopPair.{u}} (f : X ⟶ Y) :
    RelativeCochainCone.relativeDualCochainShortComplexNat R Y ⟶ RelativeCochainCone.relativeDualCochainShortComplexNat R X where
  τ₁ := Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.relativeChainFunctor R).map f)
  τ₂ := Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).map f).right
  τ₃ := Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).map f).left
  comm₁₂ := by
    change Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.relativeChainFunctor R).map f) ≫
        Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap (Cohomology.relativeChainProjection R X) =
      Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap (Cohomology.relativeChainProjection R Y) ≫
        Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).map f).right
    rw [← Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap_comp, ← Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap_comp]
    exact congrArg Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap
      ((coker.π (C := Cohomology.ChainCategory R)).naturality ((Cohomology.chainPairFunctor R).map f)).symm
  comm₂₃ := by
    change Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).map f).right ≫
        Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).obj X).hom =
      Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).obj Y).hom ≫
        Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).map f).left
    rw [← Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap_comp, ← Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap_comp]
    exact congrArg Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.chainPairFunctor R).map f).w.symm

/-- Let `R` be a commutative ring and `f: (X,A) → (Y,B)` a continuous map of topological pairs.
This is the pullback map between the sequences `C^•(Y,B;R) → C^•(Y;R) → C^•(B;R)` and
`C^•(X,A;R) → C^•(X;R) → C^•(A;R)`, after extending all singular cochain complexes by zero to
negative degrees. -/
def relativeDualCochainShortComplexIntMap {X Y : TopPair.{u}} (f : X ⟶ Y) :
    RelativeCochainCone.relativeDualCochainShortComplexInt R Y ⟶ RelativeCochainCone.relativeDualCochainShortComplexInt R X :=
  ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R)).mapShortComplex).map
    (relativeDualCochainShortComplexNatMap R f)

/-- Let `R` be a commutative ring and `f: (X,A) → (Y,B)` a continuous map of topological pairs.
This cochain map `Cone(C^•(Y;R) → C^•(B;R)) → Cone(C^•(X;R) → C^•(A;R))` is induced by pullback
on the ambient spaces and subspaces. The complexes are extended by zero to negative degrees
before forming the cones. -/
def relativeCochainConeMap {X Y : TopPair.{u}} (f : X ⟶ Y) :
    CochainComplex.mappingCone (RelativeCochainCone.relativeCochainRestrictionInt R Y) ⟶
      CochainComplex.mappingCone (RelativeCochainCone.relativeCochainRestrictionInt R X) :=
  CochainComplex.mappingCone.map _ _
    (relativeDualCochainShortComplexIntMap R f).τ₂
    (relativeDualCochainShortComplexIntMap R f).τ₃
    (relativeDualCochainShortComplexIntMap R f).comm₂₃.symm

end

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R : Type u) [CommRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical relative dual-to-cone comparison is natural. -/
@[reassoc]
lemma relativeDualCochainHomologyIsoCone_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n ≫
      (RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R X n).hom =
    (RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R Y n).hom ≫
      HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1) :=
  Algebra.Homology.DerivedCategoryConeNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone_naturality
    (relativeDualCochainShortComplexIntMap R f)
    (RelativeCochainG.relativeDualCochainShortComplexInt_shortExact R Y)
    (RelativeCochainG.relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) n (by omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Integer extension and universal coefficients preserve the
relative pullback map. -/
lemma relativeDualCochainCohomologyEquiv_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : (RelativeCochainCone.relativeDualCochainShortComplexInt R Y).X₁.homology (n : ℤ)) :
    RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv R X n
        (HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n a) =
      Cohomology.relativeCohomologyMap R n f (RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv R Y n a) :=
  ConcreteCategory.congr_hom (HomologicalComplex.extendHomologyIso_hom_naturality
    (Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap ((Cohomology.relativeChainFunctor R).map f))
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical restriction-cone comparison intertwines maps of
pairs with the relative cohomology pullback. -/
lemma relativeCochainConeCohomologyEquivCanonical_naturality
    {X Y : TopPair.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : (CochainComplex.mappingCone (RelativeCochainCone.relativeCochainRestrictionInt R Y)).homology
      ((n : ℤ) - 1)) :
    RelativeCochainConeNaturality.relativeCochainConeCohomologyEquivCanonical R X n
        (HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1) a) =
      Cohomology.relativeCohomologyMap R n f (RelativeCochainConeNaturality.relativeCochainConeCohomologyEquivCanonical R Y n a) := by
  obtain ⟨b, rfl⟩ := (RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R Y n).toLinearEquiv.surjective a
  change RelativeCochainConeNaturality.relativeCochainConeCohomologyEquivCanonical R X n
      (HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1)
        ((RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R Y n).hom b)) =
    Cohomology.relativeCohomologyMap R n f (RelativeCochainConeNaturality.relativeCochainConeCohomologyEquivCanonical R Y n
      ((RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R Y n).hom b))
  have h := ConcreteCategory.congr_hom (relativeDualCochainHomologyIsoCone_naturality R f n) b
  change (RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R X n).hom
      (HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n b) =
    HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1)
      ((RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R Y n).hom b) at h
  rw [← h]
  change RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv R X n
      ((RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R X n).toLinearEquiv.symm
        ((RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R X n).toLinearEquiv _)) =
    Cohomology.relativeCohomologyMap R n f (RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv R Y n
      ((RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R Y n).toLinearEquiv.symm
        ((RelativeCochainConeNaturality.relativeDualCochainHomologyIsoCone R Y n).toLinearEquiv b)))
  simp only [LinearEquiv.symm_apply_apply]
  exact relativeDualCochainCohomologyEquiv_naturality R f n b

end

end OAI.AlgebraicTopology.Singular.RelativeCochainIntMap
