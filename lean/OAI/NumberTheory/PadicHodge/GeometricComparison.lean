import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton

/-! # Geometric Comparison -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

attribute [local instance 2000] Submodule.module Submodule.addCommGroup Submodule.addCommMonoid
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton

namespace FrobeniusSlope

/-- The full repaired GeometricComparison proposition, copied as a type.
Its unproved statement module is deliberately not imported. -/
def GeometricComparisonInput : Prop := ∀
    {K : Type} [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime]
    (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (jq : K →+* ℚ_[q])
    (_hplace :
      (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (A : Geometry.AbelianH1Model K q jq)
    (H : Type) [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓq : ℓ ≠ q),
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ

variable {K : Type} [Field K] [NumberField K]
  (q : ℕ) [Fact q.Prime]
  (κ : K →+* AlgebraicClosure ℚ)
  (jComplex : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  (jq : K →+* ℚ_[q]) (A : Geometry.AbelianH1Model K q jq)
  (H : Type) [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
    (A.complexFiber (jComplex.comp κ)).scheme.hom)

def SummandComparisonWithNewton [FiniteDimensional ℚ_[q] A.DeRham]
    (Fil : Linear.FiniteFiltration ℚ_[q] A.DeRham) (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham) : Prop :=
  ∀ χ : H →ₐ[ℚ] AlgebraicClosure ℚ,
    A.bettiHeckeSummand (jComplex.comp κ) ρ (fun h => jComplex (χ h)) ≠ ⊥ →
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      let χq : H → AlgebraicClosure ℚ_[q] := fun h => ι (σ (χ h))
      let χc : H → ℂ := fun h => jComplex (σ (χ h))
      ∃ L : Linear.FiniteHeckeCoefficientField q χq,
        let S : Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham) :=
          A.deRhamHeckeSummand ρ χq L
        let B : Submodule ℂ (A.ComplexBetti (jComplex.comp κ)) :=
          A.bettiHeckeSummand (jComplex.comp κ) ρ χc
        letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L.field S
        ∃ φS : S ≃ₗ[L.field] S,
          (∀ x : S, (φS x : L.field ⊗[ℚ_[q]] A.DeRham) =
            Linear.coefficientFrobenius L.field φdR.toLinearMap
              (x : L.field ⊗[ℚ_[q]] A.DeRham)) ∧
          Linear.WeaklyAdmissible q (Linear.coefficientSummandFiltration L.field Fil S)
            (φS.restrictScalars ℚ_[q]) ∧
          (∀ i : ℤ,
            Module.finrank L.field
                (S ⊓ Linear.coefficientFiltration L.field A.Fil i :
                  Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham)) =
              Module.finrank ℂ
                (B ⊓ A.bettiFiltration (jComplex.comp κ) P i :
                  Submodule ℂ (A.ComplexBetti (jComplex.comp κ)))) ∧
          (∀ a : AlgebraicClosure ℚ,
            Module.End.HasEigenvalue
              (φS.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (ι a) →
              ‖jComplex a‖ = Real.sqrt (q : ℝ)) ∧
          FrobeniusSlopeComparisonNewton.NewtonData (L := L.field) (U := S) q jComplex ι φS

/-- Full comparison properties after the geometric finiteness assertions. -/
def FiniteComparisonWithNewton
    [FiniteDimensional ℚ_[q] A.DeRham] [FiniteDimensional ℚ_[q] A.Crystalline]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
    (Fil : Linear.FiniteFiltration ℚ_[q] A.DeRham),
    φ.toLinearMap = A.crystallineFrobenius ∧
    Fil.step = A.Fil ∧
    let φdR := cmp.symm.trans (φ.trans cmp)
    Linear.WeaklyAdmissible q Fil φdR ∧
    (∀ f : A.ExtendingEndomorphism,
      (∀ x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) ∧
      (∀ x, φ (A.crystallinePullback f x) = A.crystallinePullback f (φ x)) ∧
      (∀ i : ℤ, (A.Fil i).map (A.deRhamPullback f) ≤ A.Fil i)) ∧
    (∃ W : Polynomial ℤ,
      A.IsWeilPolynomial ℓ W ∧
      LinearMap.charpoly A.crystallineFrobenius = W.map (Int.castRingHom ℚ_[q]) ∧
      ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ = Real.sqrt (q : ℝ)) ∧
    (∃ (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
      (bettiCmp : A.ComplexAlgebraicDeRham (jComplex.comp κ) ≃ₗ[ℂ] A.ComplexBetti (jComplex.comp κ)),
      (∀ f : A.ExtendingEndomorphism,
        (∀ x, localCmp (A.localAlgebraicPullback f x) = A.deRhamPullback f (localCmp x)) ∧
        (∀ x, bettiCmp (A.complexAlgebraicPullback (jComplex.comp κ) f x) =
          A.complexBettiPullback (jComplex.comp κ) f (bettiCmp x))) ∧
      (∀ i : ℤ, (A.localAlgebraicFiltration i).map localCmp.toLinearMap = A.Fil i) ∧
      (∀ i : ℤ, (A.complexAlgebraicFiltration (jComplex.comp κ) i).map bettiCmp.toLinearMap =
        A.bettiFiltration (jComplex.comp κ) P i)) ∧
    SummandComparisonWithNewton q κ jComplex ι jq A H ρ P Fil φdR

/-- Statement-only target. The numerical operations are used only after
finite-dimensionality has been asserted in the conclusion. -/
def ComparisonWithNewton (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
      let := hD
      let := hC
      FiniteComparisonWithNewton q κ jComplex ι jq A H ρ P ℓ

/-- Apply the full repaired GeometricComparison input to the actual abelian variety and
upgrade all its occurring, scalar-conjugated Hecke summands with derived
weight bounds and determinant-valued Newton data. -/
theorem comparison_with_newton_from_full_GeometricComparison
    (hGeometricComparison : GeometricComparisonInput)
    (hplace :
      (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ComparisonWithNewton q κ jComplex ι jq A H ρ P ℓ := by
  obtain ⟨hD, hC, hcomp⟩ := hGeometricComparison q κ jComplex ι jq hplace A H ρ P ℓ hℓq
  let := hD
  let := hC
  obtain ⟨cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsummand⟩ := hcomp
  refine ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, ?_⟩
  obtain ⟨W, _hWdef, hchar, hweight⟩ := hW
  let φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham := cmp.symm.trans (φ.trans cmp)
  have hdRchar : LinearMap.charpoly φdR.toLinearMap = W.map (Int.castRingHom ℚ_[q]) := by
    change LinearMap.charpoly (cmp.conj φ.toLinearMap) = _
    rw [LinearEquiv.charpoly_conj, hφ, hchar]
  intro χ hχ σ
  obtain ⟨L, φS, hincl, hWAS, hdim⟩ := hsummand χ hχ σ
  refine ⟨L, φS, hincl, hWAS, hdim, ?_, ?_⟩
  · intro a ha
    exact FrobeniusSlopeComparisonNewton.weights_on_baseChanged_subspace φdR.toLinearMap W hdRchar q hweight
      (A.deRhamHeckeSummand ρ (fun h => ι (σ (χ h))) L) φS.toLinearMap
      hincl jComplex ι a ha
  · apply FrobeniusSlopeComparisonNewton.newtonData_of_weights (L := L.field)
      (U := ↥(A.deRhamHeckeSummand ρ (fun h => ι (σ (χ h))) L))
      q (Fact.out : q.Prime) jComplex ι φS
    intro a ha
    exact FrobeniusSlopeComparisonNewton.weights_on_baseChanged_subspace φdR.toLinearMap W hdRchar q hweight
      (A.deRhamHeckeSummand ρ (fun h => ι (σ (χ h))) L) φS.toLinearMap
      hincl jComplex ι a ha

/-- Forget only the proved FrobeniusSlope additions: the full repaired GeometricComparison
conclusion, with all its original operators and comparison maps, is retained. -/
theorem forget_newton (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ComparisonWithNewton q κ jComplex ι jq A H ρ P ℓ) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  obtain ⟨hD, hC, hcomp⟩ := h
  let := hD
  let := hC
  obtain ⟨cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsummand⟩ := hcomp
  refine ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, ?_⟩
  intro χ hχ σ
  obtain ⟨L, φS, hincl, hWAS, hdim, _hweight, _hnewton⟩ := hsummand χ hχ σ
  exact ⟨L, φS, hincl, hWAS, hdim⟩

end FrobeniusSlope

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
