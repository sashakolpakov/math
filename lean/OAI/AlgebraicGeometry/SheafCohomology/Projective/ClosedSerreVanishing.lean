/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
Adapted in part from the Apache-licensed `FiniteEventualUniformBound.lean`
in Vilin97/Clawristotle.
This file has been modified.
-/
import Mathlib.Data.Finset.Lattice.Fold
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SerreVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistProjectionFormula
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Closed Serre Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedSerreVanishing.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Positive-twist Cech vanishing on projective closed subschemes

The projective-space positive-twist vanishing theorem transfers to a closed
subscheme by pushforward, the projective-twist projection formula, and the
ordered-Cech comparison for an inverse-image cover.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal MonoidalCategory
  TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance closedPositiveTwistMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

private theorem exists_uniform_eventual_bound
    {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop)
    (hP : ∀ i, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → P i n) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ i, P i n := by
  classical
  choose bound hbound using hP
  let b := Finset.univ.sup bound
  refine ⟨b, fun n hn i ↦ hbound i n ?_⟩
  exact (Finset.le_sup (f := bound) (Finset.mem_univ i)).trans hn

/-- A finite-type quasicoherent module on a closed subscheme of polynomial
projective space has exact inverse-image-cover ordered-Cech complex in each
fixed positive degree after every sufficiently large pulled-back positive
coordinate twist. -/
theorem closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (q : ℕ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N →
      (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ (Scheme.Modules.pullback f).obj
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N))
        (fun i => f ⁻¹ᵁ StandardCech.MvPolynomial.coordinateOpenCover
          (R := R) (σ := σ) i)).ExactAt (q + 1) := by
  let N := (Scheme.Modules.pushforward f).obj M
  let : N.IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  let : N.IsFiniteType :=
    Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f
  obtain ⟨b, hb⟩ :=
    SerreVanishing.MvPolynomial.finiteType_eventually_orderedBaseCechComplex_exactAt_succ N j q
  refine ⟨b, fun n hn ↦ ?_⟩
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let T : X.Modules := M ⊗ (Scheme.Modules.pullback f).obj P
  let ePF : N ⊗ P ≅ (Scheme.Modules.pushforward f).obj T :=
    (TwistProjectionFormula.MvPolynomial.coordinateHyperplanePoleSheafPowerPushforwardTensorIso f j n).app M
  let F := OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
  let eC :
      OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
          (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) T
          (fun i => f ⁻¹ᵁ StandardCech.MvPolynomial.coordinateOpenCover
            (R := R) (σ := σ) i) ≅
        OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (N ⊗ P)
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) :=
    OrderedBaseCechPushforward.Scheme.Modules.orderedBaseCechComplexPushforwardIso f
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) T
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) ≪≫
      (F.mapIso ePF).symm
  have hN := hb n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hN ⊢
  exact
    (HomologicalComplex.homologyMapIso eC (q + 1)).isZero_iff.mpr hN

/-- A finite-type quasicoherent module on a closed subscheme of polynomial
projective space has exact inverse-image-cover ordered-Cech complex in every
positive degree after one sufficiently large pulled-back positive coordinate
twist. -/
theorem
    closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_of_pos
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N → ∀ q : ℕ, 0 < q →
      (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ (Scheme.Modules.pullback f).obj
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N))
        (fun i => f ⁻¹ᵁ StandardCech.MvPolynomial.coordinateOpenCover
          (R := R) (σ := σ) i)).ExactAt q := by
  let d := Fintype.card (ULift.{u} σ)
  let P : Fin d → ℕ → Prop := fun q N ↦
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (M ⊗ (Scheme.Modules.pullback f).obj
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N))
      (fun i => f ⁻¹ᵁ StandardCech.MvPolynomial.coordinateOpenCover
        (R := R) (σ := σ) i)).ExactAt (q.1 + 1)
  obtain ⟨b, hb⟩ := exists_uniform_eventual_bound P fun q ↦
    closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_succ
      f M j q.1
  refine ⟨b, fun N hN q hq ↦ ?_⟩
  by_cases hdq : d ≤ q
  · exact OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
      (f ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (M ⊗ (Scheme.Modules.pullback f).obj
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N))
      (fun i => f ⁻¹ᵁ StandardCech.MvPolynomial.coordinateOpenCover
        (R := R) (σ := σ) i) q hdq
  · have hqd : q - 1 < d := by omega
    have hP := hb N hN ⟨q - 1, hqd⟩
    simpa [P, Nat.sub_add_cancel hq] using hP

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedSerreVanishing.MvPolynomial
