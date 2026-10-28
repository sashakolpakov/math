/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistCoproduct
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence

/-! # Positive Twist Tensor Cech -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistTensorCech.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Cech exactness after an additional positive projective twist

Positive coordinate twists add under tensor product. Consequently,
tensoring a finite coproduct of positive twists by another positive twist
preserves its positive-degree ordered-Cech exactness.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomogeneousIdeal
  MonoidalCategory Opposite TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance positiveTwistTensorMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- Reassociating two positive coordinate twists adds their degrees. -/
noncomputable def moduleTensorCoordinateHyperplanePoleSheafPowerAddIso
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    (j : σ) (m n : ℕ) :
    (M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
      M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n) :=
  α_ M
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) ≪≫
    (Iso.refl M ⊗ᵢ
      (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso
        (R := R) j m n).symm)

/-- Tensoring a finite coproduct of positive coordinate twists by another
positive twist adds its degree to every summand. -/
noncomputable def
    coordinateHyperplanePoleSheafPowerCoproductTensorIso
    {I : Type} [Finite I] (j : σ) (n : I → ℕ) (N : ℕ) :
    (∐ fun i : I ↦
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n i)) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N ≅
      ∐ fun i : I ↦
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n i + N) := by
  let E :=
    PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence
      (R := R) j N
  let L : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n i)
  let P : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n i + N)
  let e₀ : E.functor.obj (∐ L) ≅ ∐ fun i ↦ E.functor.obj (L i) :=
    PreservesCoproduct.iso E.functor L
  let e₁ : (∐ fun i ↦ E.functor.obj (L i)) ≅ ∐ P :=
    Sigma.mapIso fun i =>
      (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso
        (R := R) j (n i) N).symm
  exact e₀ ≪≫ e₁

/-- A finite coproduct of positive twists remains ordered-Cech acyclic in
positive degrees after tensoring by another positive twist. -/
theorem
    coordinateHyperplanePoleSheafPowerCoproductTensor_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] {I : Type} [Finite I]
    (j : σ) (n : I → ℕ) (N q : ℕ) :
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      ((∐ fun i : I ↦
          TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n i)) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N)
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).ExactAt (q + 1) := by
  let F :=
    OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
  let e :=
    coordinateHyperplanePoleSheafPowerCoproductTensorIso
      (R := R) j n N
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply
    (HomologicalComplex.homologyMapIso
      (F.mapIso e) (q + 1)).isZero_iff.mpr
  apply HomologicalComplex.ExactAt.isZero_homology
  exact
    PositiveTwistCoproduct.MvPolynomial.coordinateHyperplanePoleSheafPowerCoproduct_orderedBaseCechComplex_exactAt_succ
      (R := R) (fun _ : I ↦ j) (fun i ↦ n i + N) q

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistTensorCech.MvPolynomial
