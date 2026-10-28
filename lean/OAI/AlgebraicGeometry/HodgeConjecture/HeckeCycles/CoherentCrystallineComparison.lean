import OAI.NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline

/-! # Coherent Crystalline Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoherentCrystallineComparison.CM

noncomputable section

/-! Retain naturality and the verified purity data from one choice of the
full GeometricComparison comparison. The Frobenius polynomial is transported through
that same comparison, with the given actual Hecke realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

attribute [local instance 2000] Submodule.module Submodule.addCommGroup Submodule.addCommMonoid

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
  (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
    (A.complexFiber (jComplex.comp κ)).scheme.hom)

theorem purity_of_same_summands
    [FiniteDimensional ℚ_[q] A.DeRham]
    [FiniteDimensional ℂ (A.ComplexBetti (jComplex.comp κ))]
    (Fil : NumberTheory.PadicHodge.GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham) (hFil : Fil.step = A.Fil)
    (φdR : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (hsumm : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.SummandComparisonWithNewton
      q κ jComplex iota jq A H ρ P Fil φdR) :
    NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter.VerifiedNativePurityComparison A κ jComplex iota H ρ P Fil φdR := by
  apply NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter.verified_native_purity_comparison A κ jComplex iota H ρ P Fil φdR
  intro χ hχ σ
  obtain ⟨L, φS, hφS, hWAS, hcompS, hweights, hdata⟩ := hsumm χ hχ σ
  have hn := NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.summand_comparison_numbers A (jComplex.comp κ) H ρ P
    (fun h => iota (σ (χ h))) (fun h => jComplex (σ (χ h)))
    L Fil hFil φS hWAS hcompS
  refine ⟨L, φS, hφS, hWAS, hweights, hdata,
    NumberTheory.PadicHodge.Filtration.CM.ExtremeSlopesAdapter.coefficient_weaklyAdmissible01 q L.field Fil _ φS hWAS hn.2.1 hn.2.2.1,
    hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2, ?_⟩
  exact NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter.intrinsic_newton_eq_hodge_of_comparison q L.field
    (V := A.deRhamHeckeSummand ρ (fun h => iota (σ (χ h))) L) φS _ hn.2.2.2.2

theorem natural_comparison_from_full_GeometricComparison
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = iota.comp κ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
    ∃ hB : FiniteDimensional ℂ (A.ComplexBetti (jComplex.comp κ)),
      letI := hD
      letI := hC
      letI := hB
      ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
        (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
        (Fil : NumberTheory.PadicHodge.GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham),
        φ.toLinearMap = A.crystallineFrobenius ∧ Fil.step = A.Fil ∧
        (∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) ∧
        NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter.VerifiedNativePurityComparison A κ jComplex iota H ρ P Fil
          (cmp.symm.trans (φ.trans cmp)) := by
  obtain ⟨hD, hC, hcomp⟩ := NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.comparison_with_newton_from_full_GeometricComparison
    q κ jComplex iota jq A H ρ P (@hGeometricComparison) hplace ℓ hℓq
  let := hD
  let := hC
  obtain ⟨cmp, φ, Fil, hφ, hFil, _hWA, hfun, _hweil, hgeo, hsumm⟩ := hcomp
  obtain ⟨localCmp, bettiCmp, _hgeo⟩ := hgeo
  have hB := NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.complex_finite_of_comparisons A (jComplex.comp κ) localCmp bettiCmp
  exact ⟨hD, hC, hB, cmp, φ, Fil, hφ, hFil, (fun f => (hfun f).1),
    purity_of_same_summands A κ jComplex iota ρ P Fil hFil _ hsumm⟩

theorem polynomial_and_purity_from_full_GeometricComparison
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = iota.comp κ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (h : Fin 3 → H)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A.specialFiber.scheme)
      (fun i => Specialized.CM.Hecke.specializedHeckeAction A ρ (h i)) = 0) :
    ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
    ∃ hB : FiniteDimensional ℂ (A.ComplexBetti (jComplex.comp κ)),
      letI := hD
      letI := hC
      letI := hB
      ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
        (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
        (Fil : NumberTheory.PadicHodge.GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham),
        φ.toLinearMap = A.crystallineFrobenius ∧ Fil.step = A.Fil ∧
        let φdR := cmp.symm.trans (φ.trans cmp)
        (∀ h k, Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k)) ∧
        (∀ h, Commute φdR.toLinearMap (A.deRhamHecke ρ h)) ∧
        Ordinary.Polynomial.CM.heckePolynomialValue q φdR.toLinearMap
          (fun i => A.deRhamHecke ρ (h i)) = 0 ∧
        NumberTheory.PadicHodge.ExtremeSlopesNewtonSummands.CM.Adapter.VerifiedNativePurityComparison A κ jComplex iota H ρ P Fil φdR := by
  obtain ⟨hD, hC, hB, cmp, φ, Fil, hφ, hFil, hc, hpurity⟩ :=
    natural_comparison_from_full_GeometricComparison A κ jComplex iota ρ P hGeometricComparison hplace ℓ hℓq
  let := hD
  let := hC
  let := hB
  have hgroup := CrystallineGroupLaw.CM.groupLaw_from_full_GeometricComparison
    A hGeometricComparison κ jComplex iota hplace P ℓ hℓq
  have hpoly := HeckeCycles.Crystalline.CM.Hecke.deRham_polynomial_from_crystalline A ρ cmp hc h
    (HeckeCycles.Crystalline.CM.Hecke.crystalline_polynomial_from_specialized A ρ hgroup h hp)
  have hf := HeckeCycles.Crystalline.CM.Hecke.comparisonFrobenius_linear A cmp φ hφ
  refine ⟨hD, hC, hB, cmp, φ, Fil, hφ, hFil,
    HeckeCycles.Crystalline.CM.Hecke.deRhamHecke_commute A ρ hgroup cmp hc, ?_, ?_, hpurity⟩
  · intro k
    rw [← hf]
    exact HeckeCycles.Crystalline.CM.Hecke.deRhamFrobenius_hecke_commute A ρ hgroup cmp hc k
  · rwa [← hf]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoherentCrystallineComparison.CM
