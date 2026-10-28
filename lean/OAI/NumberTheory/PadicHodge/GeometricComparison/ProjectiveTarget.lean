import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveSummand
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveIntrinsicAdmissibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Naturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.NaturalityCriterion
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeilFrobeniusInvertibility

/-! # Projective Target -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The full original target from the constructed native comparison and
the proved projective complex comparison. The remaining arithmetic
inputs are the weights and the actual shared characteristic polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.projective_comparisonTarget_of_shared_polynomial
    [FiniteDimensional ℚ_[q] A.Crystalline]
    (hCompletion : Completion.GeometricWeightInput.{0})
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (W : Polynomial ℤ) (hW : A.IsWeilPolynomial ℓ W)
    (hCW : A.crystallineFrobenius.charpoly = W.map (Int.castRingHom ℚ_[q])) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  let hD : FiniteDimensional ℚ_[q] A.DeRham :=
    A.localDeRham_finite_of_projective_comparison (jComplex.comp κ) P
  let : FiniteDimensional ℚ_[q] A.DeRham := hD
  let hC : FiniteDimensional ℚ_[q] A.Crystalline := inferInstance
  let cmp := A.constructedCrystallineDeRhamEquiv
  let φ := LinearEquiv.ofBijective A.crystallineFrobenius
    (WeilFrobeniusInvertibility.WeilDeterminant.bijective q A.crystallineFrobenius W hCW
      (A.native_polynomial_weights hCompletion ℓ hℓq W hW))
  have hφ : φ.toLinearMap = A.crystallineFrobenius := rfl
  let φdR := WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv cmp φ
  have hnat (f : A.ExtendingEndomorphism) (x : A.Crystalline) :
      cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x) :=
    A.constructedCrystallineDeRhamEquiv_naturality_of_integral f
      (A.constructedIntegralCrystallineEquiv_naturality f) x
  have hWA : Linear.WeaklyAdmissible q A.finiteFiltration φdR :=
    A.projective_constructedComparison_weaklyAdmissible hCompletion
      (jComplex.comp κ) P ℓ hℓq W hW hCW φ hφ
  have hcrys (f : A.ExtendingEndomorphism) : Commute (A.crystallinePullback f) φ.toLinearMap := by
    rw [hφ]
    exact (A.crystallineFrobenius_commutes f).symm
  have hcomm (f : A.ExtendingEndomorphism) : Commute (A.deRhamPullback f) φdR.toLinearMap :=
    HeckeCommutation.GeneralizedHecke.conjugate_commutes cmp (A.crystallinePullback f) (A.deRhamPullback f)
      φ (hnat f) (hcrys f)
  refine ⟨hD, hC, cmp, φ, A.finiteFiltration,
    hφ, rfl, hWA, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨hnat f, ?_, A.deRhamPullback_preservesFil f⟩
    intro x
    exact DFunLike.congr_fun (hcrys f).symm.eq x
  · exact ⟨W, hW, hCW, A.native_polynomial_weights hCompletion ℓ hℓq W hW⟩
  · exact A.projective_algebraic_filtered_comparisons (jComplex.comp κ) P
  · exact A.projective_summandComparison_for_frobenius κ jComplex ι hplace ρ P φdR hcomm hWA

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
