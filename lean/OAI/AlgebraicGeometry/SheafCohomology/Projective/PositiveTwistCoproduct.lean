/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechHigher
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor

/-! # Positive Twist Coproduct -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistCoproduct.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Cech exactness for finite coproducts of positive projective twists

The ordered standard-cover Cech complex of a finite coproduct of
nonnegative coordinate twists is exact in every positive degree.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Finite coproducts of nonnegative coordinate twists are ordered-Cech
acyclic in every positive degree. -/
theorem coordinateHyperplanePoleSheafPowerCoproduct_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] {I : Type} [Finite I]
    (j : I → σ) (n : I → ℕ) (q : ℕ) :
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (∐ fun i : I ↦ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) (j i) (n i))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).ExactAt (q + 1) := by
  classical
  let := Fintype.ofFinite I
  let : HasFiniteBiproducts (Proj (homogeneousSubmodule σ R)).Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : HasFiniteBiproducts
      (ModuleCat.{u}
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let M : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) (j i) (n i)
  let F := OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{u}
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)))
      (ComplexShape.up ℕ) (q + 1)
  let : F.Additive := by
    dsimp only [F]
    infer_instance
  let : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  have hcomponent (i : I) : IsZero (F.obj (M i)) := by
    change IsZero
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) (j i) (n i))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology (q + 1))
    apply HomologicalComplex.ExactAt.isZero_homology
      (TwistCechHigher.MvPolynomial.coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_succ
        (R := R) (j i) (n i : ℤ) (Int.natCast_nonneg (n i)) q)
  let (i : I) : Subsingleton (F.obj (M i)) :=
    ModuleCat.subsingleton_of_isZero (hcomponent i)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  change IsZero (F.obj (∐ M))
  let e₀ : F.obj (∐ M) ≅ F.obj (⨁ M) :=
    F.mapIso (biproduct.isoCoproduct M).symm
  let e₁ : F.obj (⨁ M) ≅ ⨁ (F.obj ∘ M) := F.mapBiproduct M
  let e₂ : (⨁ (F.obj ∘ M)) ≅ ∏ᶜ (F.obj ∘ M) :=
    biproduct.isoProduct (F.obj ∘ M)
  let e₃ : (∏ᶜ (F.obj ∘ M)) ≅
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (∀ i : I, F.obj (M i)) :=
    ModuleCat.piIsoPi (F.obj ∘ M)
  apply (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃).isZero_iff.mpr
  exact ModuleCat.isZero_of_subsingleton _

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistCoproduct.MvPolynomial
