/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FixedNegativeQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence

/-! # Shifted Quotient -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ShiftedQuotient.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Shifted presentations by projective twists

Tensoring a fixed-coordinate negative-twist presentation by a sufficiently
large positive twist produces a presentation by nonnegative twists.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomogeneousIdeal
  MonoidalCategory

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance shiftedPresentationMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- Tensoring a finite coproduct of fixed-coordinate negative twists by a
sufficiently large positive twist produces nonnegative twists. -/
noncomputable def fixedCoordinateNegativeTwistCoproductTensorIso
    (j : σ) {r : ℕ} (d : Fin r → ℕ) (N : ℕ)
    (hN : ∀ i, d i ≤ N) :
    (∐ fun i : Fin r ↦
        TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N ≅
      ∐ fun i : Fin r ↦
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - d i) := by
  let E := PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence
    (R := R) j N
  let L : Fin r → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  let P : Fin r → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - d i)
  let e₀ : E.functor.obj (∐ L) ≅ ∐ fun i ↦ E.functor.obj (L i) :=
    PreservesCoproduct.iso E.functor L
  let e₁ : (∐ fun i ↦ E.functor.obj (L i)) ≅ ∐ P :=
    Sigma.mapIso fun i =>
      TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE
        (R := R) j (d i) N (hN i)
  exact e₀ ≪≫ e₁

/-- After one fixed positive twist, a finite-type quasicoherent module is a
quotient of finitely many nonnegative powers of the same coordinate twist. -/
theorem exists_fin_coordinateNonnegativeTwist_quotient [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (N : ℕ)
        (f : (∐ fun i : Fin r ↦
          TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - d i)) ⟶
            M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N),
      Epi f := by
  classical
  obtain ⟨r, d, f, hf⟩ :=
    FixedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient M j
  let : Epi f := hf
  let N := Finset.univ.sup d
  have hN (i : Fin r) : d i ≤ N :=
    Finset.le_sup (Finset.mem_univ i)
  let E := PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence
    (R := R) j N
  let : E.functor.PreservesEpimorphisms := inferInstance
  let e := fixedCoordinateNegativeTwistCoproductTensorIso
    (R := R) j d N hN
  let g : (∐ fun i : Fin r ↦
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - d i)) ⟶
        M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N :=
    e.inv ≫ E.functor.map f
  refine ⟨r, d, N, g, ?_⟩
  change Epi (e.inv ≫ E.functor.map f)
  exact @epi_comp _ _ _ _ _ e.inv (by infer_instance)
    (E.functor.map f) (E.functor.map_epi f)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ShiftedQuotient.MvPolynomial
