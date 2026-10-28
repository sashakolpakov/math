import OAI.NumberTheory.PadicHodge.IntrinsicSummands
import OAI.NumberTheory.PadicHodge.IntrinsicOrdinary
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline

/-! # Intrinsic Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntrinsicComparison.FrobeniusSlopeIntrinsic

noncomputable section

/-! Preserve the full GeometricComparison comparison while transporting the geometric
CubicRelation polynomial to the exact summands used by the native slope proof. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke
open OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (κ : K →+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
    (A.complexFiber (j.comp κ)).scheme.hom)

/-- All GeometricComparison conclusions, with the same comparison and Frobenius,
plus the resolved FrobeniusSlope result on the specified native character. -/
def FiniteComparisonForced
    [FiniteDimensional ℚ_[q] A.DeRham] [FiniteDimensional ℚ_[q] A.Crystalline]
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ)
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (φ : A.Crystalline ≃ₗ[ℚ_[q]] A.Crystalline)
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] A.DeRham),
    φ.toLinearMap = A.crystallineFrobenius ∧
    Fil.step = A.Fil ∧
    let φdR := cmp.symm.trans (φ.trans cmp)
    GeometricComparison.Linear.WeaklyAdmissible q Fil φdR ∧
    (∀ f : A.ExtendingEndomorphism,
      (∀ x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x)) ∧
      (∀ x, φ (A.crystallinePullback f x) = A.crystallinePullback f (φ x)) ∧
      (∀ i : ℤ, (A.Fil i).map (A.deRhamPullback f) ≤ A.Fil i)) ∧
    (∃ W : Polynomial ℤ,
      A.IsWeilPolynomial ℓ W ∧
      LinearMap.charpoly A.crystallineFrobenius = W.map (Int.castRingHom ℚ_[q]) ∧
      ∀ z : ℂ, Polynomial.aeval z W = 0 → ‖z‖ = Real.sqrt (q : ℝ)) ∧
    (∃ (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
      (bettiCmp : A.ComplexAlgebraicDeRham (j.comp κ) ≃ₗ[ℂ] A.ComplexBetti (j.comp κ)),
      (∀ f : A.ExtendingEndomorphism,
        (∀ x, localCmp (A.localAlgebraicPullback f x) = A.deRhamPullback f (localCmp x)) ∧
        (∀ x, bettiCmp (A.complexAlgebraicPullback (j.comp κ) f x) =
          A.complexBettiPullback (j.comp κ) f (bettiCmp x))) ∧
      (∀ i : ℤ, (A.localAlgebraicFiltration i).map localCmp.toLinearMap = A.Fil i) ∧
      (∀ i : ℤ, (A.complexAlgebraicFiltration (j.comp κ) i).map bettiCmp.toLinearMap =
        A.bettiFiltration (j.comp κ) P i)) ∧
    (GeometricComparison.HeckeScalar.SummandComparison q κ j ι jq A H ρ P Fil φdR ∧
      IntrinsicSummands.FrobeniusSlopeIntrinsicComparison.SummandForced A κ j ι ρ P Fil φdR χ r b e)

def ComparisonForced
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ) (r b e : AlgebraicClosure ℚ)
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∃ hD : FiniteDimensional ℚ_[q] A.DeRham,
    ∃ hC : FiniteDimensional ℚ_[q] A.Crystalline,
      let := hD
      let := hC
      FiniteComparisonForced A κ j ι ρ P χ r b e ℓ

theorem comparison_forced_from_full_GeometricComparison
    (hGeometricComparison : GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (idx : Fin 3 → H)
    (hp : AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) A.specialFiber.scheme)
      (fun i => AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction A ρ (idx i)) = 0)
    (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (hχ : A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (χ h)) ≠ ⊥)
    (r b e : AlgebraicClosure ℚ) (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : j r = (Real.sqrt (q : ℝ) : ℂ)) (heC : ‖j e‖ = 1)
    (hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1)
    (hvalues : ∀ i, χ (idx i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b e i) :
    ComparisonForced A κ j ι ρ P χ r b e ℓ := by
  obtain ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsumm⟩ :=
    hGeometricComparison q κ j ι jq hplace A H ρ P ℓ hℓq
  let := hD
  let := hC
  refine ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsumm, ?_⟩
  have hc := fun f => (hfun f).1
  have hgroup := AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineGroupLaw.CM.groupLaw_from_full_GeometricComparison
    A (@hGeometricComparison) κ j ι hplace P ℓ hℓq
  have hpoly := AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke.deRham_polynomial_from_crystalline A ρ cmp hc idx
    (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke.crystalline_polynomial_from_specialized A ρ hgroup idx hp)
  have hf := AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke.comparisonFrobenius_linear A cmp φ hφ
  rw [hf] at hpoly
  have hfcomm : ∀ h, Commute (cmp.symm.trans (φ.trans cmp)).toLinearMap
      (A.deRhamHecke ρ h) := by
    intro h
    rw [← hf]
    exact AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke.deRhamFrobenius_hecke_commute A ρ hgroup cmp hc h
  obtain ⟨W, _hweil, hchar, hweight⟩ := hW
  have hcharD : LinearMap.charpoly (cmp.symm.trans (φ.trans cmp)).toLinearMap =
      W.map (Int.castRingHom ℚ_[q]) := by
    change LinearMap.charpoly (cmp.conj φ.toLinearMap) = _
    rw [LinearEquiv.charpoly_conj, hφ, hchar]
  exact IntrinsicSummands.FrobeniusSlopeIntrinsicComparison.forced_on_same_summands A κ j ι ρ P Fil _ hsumm W hcharD hweight
    (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Crystalline.CM.Hecke.deRhamHecke_commute A ρ hgroup cmp hc) hfcomm idx hpoly
    χ hχ r b e hr hrC heC hcentral hvalues

/-- Dropping only the FrobeniusSlope conclusions recovers the full GeometricComparison target. -/
theorem forget_forced (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (r b e : AlgebraicClosure ℚ) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ComparisonForced A κ j ι ρ P χ r b e ℓ) :
    GeometricComparison.HeckeScalar.ComparisonTarget q κ j ι jq A H ρ P ℓ := by
  obtain ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsumm, _hforced⟩ := h
  let := hD
  let := hC
  exact ⟨hD, hC, cmp, φ, Fil, hφ, hFil, hWA, hfun, hW, hbase, hsumm⟩

end

end OAI.NumberTheory.PadicHodge.IntrinsicComparison.FrobeniusSlopeIntrinsic
