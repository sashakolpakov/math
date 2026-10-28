import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Projectors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Purity
import OAI.LinearAlgebra.Endomorphisms.Commuting

/-! # Comparison Embedding Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ComparisonEmbeddingPurity.CM

noncomputable section

section

/-! Apply the constructed comparison to the exact transported projector.
All operator, valuation-normalization and Hodge-projector premises are
discharged. The remaining inputs are the arithmetic values and signs of
the same character. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ProjectorTransport.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
  (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (idx : Fin 3 → H)

local notation "j" => jComplex.comp κ

theorem bounds_on_same_projector
    (hc : Comparison.CM.Conclusion A κ jComplex iota ρ idx)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (hχ : A.bettiHeckeSummand j ρ (fun h => jComplex (χ h)) ≠ ⊥)
    (τ : Gal(AlgebraicClosure ℚ/ℚ))
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (hP : P ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (Comap.CM.hodge A j) (Comap.CM.hodge A j))
    (hRange : LinearMap.range (Intrinsic.ProjectorTransport.CM.projector A j P) =
      A.bettiHeckeSummand j ρ (fun h => jComplex (τ (χ h))))
    (hne : LinearMap.range (Intrinsic.ProjectorTransport.CM.projector A j P) ≠ ⊥)
    (r b e : AlgebraicClosure ℚ) (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : jComplex r = (Real.sqrt (q : ℝ) : ℂ))
    (heC : ‖jComplex e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (hvalues : ∀ i : Fin 3, τ (χ (idx i)) =
      (![(q : AlgebraicClosure ℚ) * b * (r + r⁻¹ + e),
        (q : AlgebraicClosure ℚ) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
        b ^ 3 * e] : Fin 3 → AlgebraicClosure ℚ) i)
    (sign : Bool) (initial : ℚ)
    (hinitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hsign : NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (iota e) = (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial) :
    let slope : ℚ := 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial / 3
    (slope = 0 ∨ slope = 1) ∧
      (slope = 1 ↔ LinearMap.range P ≤ (Comap.CM.hodge A j).holomorphic) ∧
      (slope = 0 ↔ LinearMap.range P ≤ (Comap.CM.hodge A j).antiholomorphic) := by
  obtain ⟨hD, hC, hB, hc⟩ := hc
  let := hD
  let := hC
  let := hB
  obtain ⟨cmp, φ, Fil, _hφ, _hFil, hcomm, hfcomm, hpoly, hcomp⟩ := hc
  let f := cmp.symm.trans (φ.trans cmp)
  obtain ⟨L, φS, hincl, _hWA, _hweight, _hdata, _hWA01, _hdim,
    _h0, _h2, _h1, _hraw, _hnewton, hpurity⟩ := hcomp χ hχ τ
  have h67 : NumberTheory.PadicHodge.FrobeniusSlopeComparisonNewton.CommutingInput (AlgebraicClosure ℚ_[q])
      ((AlgebraicClosure ℚ_[q]) ⊗[L.field]
        (A.deRhamHeckeSummand ρ (fun h => iota (τ (χ h))) L)) := by
    intro T hT
    exact LinearAlgebra.Endomorphisms.Commuting.Construction.commuting_family_structure T hT
  have he : iota e ≠ 0 := by
    apply (map_ne_zero iota).mpr
    intro hz
    exact zero_ne_one (by simpa only [hz, map_zero, norm_zero] using heC)
  have hresult := Intrinsic.Purity.CM.purity_from_native_operators
    A ρ hcomm (fun h => iota (τ (χ h))) L f.toLinearMap φS hincl hfcomm idx hpoly
    jComplex iota _ _ _ hpurity r b e hr hrC heC hcentral
    (fun i => congrArg iota (hvalues i)) h67
    (NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation q) (NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation_q q)
    (NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (iota e)) (NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.canonicalAddValuation_apply q _ he)
    (Intrinsic.ProjectorTransport.CM.complementary A j) (Intrinsic.ProjectorTransport.CM.projector A j P) hRange
    (Intrinsic.ProjectorTransport.CM.projector_holomorphic A j P hP) (Intrinsic.ProjectorTransport.CM.projector_antiholomorphic A j P hP)
    (hRange ▸ hne) sign initial hinitial hsign
  have hh := Intrinsic.ProjectorTransport.CM.holomorphic_bound_iff A j (LinearMap.range P)
  have ha := Intrinsic.ProjectorTransport.CM.antiholomorphic_bound_iff A j (LinearMap.range P)
  rw [← Intrinsic.ProjectorTransport.CM.projector_range, hRange] at hh ha
  exact ⟨hresult.1, hresult.2.1.trans hh, hresult.2.2.trans ha⟩

end

/-! Express the constructed purity theorem at an equal, specified complex
embedding. The algebraic-closure and local comparison maps stay fixed. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ProjectorTransport.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
  (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
  (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (idx : Fin 3 → H)
  (j : K →+* ℂ) (hj : jComplex.comp κ = j)

include hj in
theorem bounds
    (hc : Comparison.CM.Conclusion A κ jComplex iota ρ idx)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (hχ : A.bettiHeckeSummand j ρ (fun h => jComplex (χ h)) ≠ ⊥)
    (τ : Gal(AlgebraicClosure ℚ/ℚ))
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification (A.Betti j)))
    (hP : P ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (Comap.CM.hodge A j) (Comap.CM.hodge A j))
    (hRange : LinearMap.range (Intrinsic.ProjectorTransport.CM.projector A j P) =
      A.bettiHeckeSummand j ρ (fun h => jComplex (τ (χ h))))
    (hne : LinearMap.range (Intrinsic.ProjectorTransport.CM.projector A j P) ≠ ⊥)
    (r b e : AlgebraicClosure ℚ) (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : jComplex r = (Real.sqrt (q : ℝ) : ℂ))
    (heC : ‖jComplex e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (hvalues : ∀ i : Fin 3, τ (χ (idx i)) =
      (![(q : AlgebraicClosure ℚ) * b * (r + r⁻¹ + e),
        (q : AlgebraicClosure ℚ) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e),
        b ^ 3 * e] : Fin 3 → AlgebraicClosure ℚ) i)
    (sign : Bool) (initial : ℚ)
    (hinitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hsign : NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (iota e) = (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial) :
    let slope : ℚ := 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * initial / 3
    (slope = 0 ∨ slope = 1) ∧
      (slope = 1 ↔ LinearMap.range P ≤ (Comap.CM.hodge A j).holomorphic) ∧
      (slope = 0 ↔ LinearMap.range P ≤ (Comap.CM.hodge A j).antiholomorphic) := by
  subst j
  exact bounds_on_same_projector A κ jComplex iota ρ idx
    hc χ hχ τ P hP hRange hne r b e hr hrC heC hcentral hvalues sign initial hinitial hsign

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ComparisonEmbeddingPurity.CM
