import OAI.NumberTheory.PadicHodge.GeometricComparisonAdapter
import Mathlib.RingTheory.Flat.Basic

/-! # Comparison Relations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonRelations.CM

noncomputable section

/-! Integer linear relations between actual extending-endomorphism
pullbacks pass from Betti H1 to crystalline H1 through the full GeometricComparison
comparison. Faithful scalar extension descends the complex relation to
the number field before extending it at the specified q-adic place. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

section Linear

variable {F V W J : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

theorem relation_iff (e : V ≃ₗ[F] W) (T : J → Module.End F V)
    (U : J → Module.End F W) (h : ∀ i x, e (T i x) = U i (e x))
    (I : Finset J) (c : J → ℤ) :
    (∑ i ∈ I, c i • T i) = 0 ↔ (∑ i ∈ I, c i • U i) = 0 := by
  have he (x : V) :
      e ((∑ i ∈ I, c i • T i) x) = (∑ i ∈ I, c i • U i) (e x) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, h]
  constructor
  · intro ht
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← he, ht]
    simp only [LinearMap.zero_apply, map_zero]
  · intro hu
    apply LinearMap.ext
    intro x
    apply e.injective
    rw [he, hu]
    simp only [LinearMap.zero_apply, map_zero]

variable {L : Type*} [Field L] [Algebra F L]

theorem scalar_relation_iff (T : J → Module.End F V) (I : Finset J) (c : J → ℤ) :
    (∑ i ∈ I, c i • T i) = 0 ↔ (∑ i ∈ I, c i • (T i).baseChange L) = 0 := by
  let bc := LinearMap.baseChangeHom F L V V
  have he : bc (∑ i ∈ I, c i • T i) = ∑ i ∈ I, c i • (T i).baseChange L := by
    simp only [map_sum, map_zsmul]
    rfl
  constructor
  · intro ht
    rw [← he, ht, map_zero]
  · intro ht
    apply LinearMap.baseChangeHom_injective F V L
    rw [he, ht, map_zero]

end Linear

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

theorem betti_relation_implies_crystalline
    (j : K →+* ℂ)
    (cmp : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham)
    (localCmp : A.LocalAlgebraicDeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (bettiCmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j)
    (hcris : ∀ f x, cmp (A.crystallinePullback f x) = A.deRhamPullback f (cmp x))
    (hloc : ∀ f x, localCmp (A.localAlgebraicPullback f x) = A.deRhamPullback f (localCmp x))
    (hbetti : ∀ f x, bettiCmp (A.complexAlgebraicPullback j f x) =
      A.complexBettiPullback j f (bettiCmp x))
    {J : Type*} (I : Finset J) (f : J → A.ExtendingEndomorphism) (c : J → ℤ)
    (h : (∑ i ∈ I, c i • A.complexBettiPullback j (f i)) = 0) :
    (∑ i ∈ I, c i • A.crystallinePullback (f i)) = 0 := by
  let : Algebra K ℂ := j.toAlgebra
  let : Algebra K ℚ_[q] := jq.toAlgebra
  have hcomplex := (relation_iff bettiCmp
    (fun i => A.complexAlgebraicPullback j (f i))
    (fun i => A.complexBettiPullback j (f i)) (fun i => hbetti (f i)) I c).mpr h
  have halg := (scalar_relation_iff (L := ℂ)
    (fun i => A.algebraicDeRhamPullback (f i)) I c).mpr hcomplex
  have hlocal := (scalar_relation_iff (L := ℚ_[q])
    (fun i => A.algebraicDeRhamPullback (f i)) I c).mp halg
  have hdr := (relation_iff localCmp
    (fun i => A.localAlgebraicPullback (f i)) (fun i => A.deRhamPullback (f i))
    (fun i => hloc (f i)) I c).mp hlocal
  exact (relation_iff cmp
    (fun i => A.crystallinePullback (f i)) (fun i => A.deRhamPullback (f i))
    (fun i => hcris (f i)) I c).mpr hdr

/-- All comparison maps and naturality equations here are extracted from
the complete prerequisite conclusion, with no additive-action premise. -/
theorem crystalline_relations_of_full_comparison
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (iota : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hcomparison : NumberTheory.PadicHodge.GeometricComparison.HeckeScalar.ComparisonTarget q κ jComplex iota jq A H ρ P ℓ)
    {J : Type*} (I : Finset J) (f : J → A.ExtendingEndomorphism) (c : J → ℤ)
    (h : (∑ i ∈ I, c i • A.complexBettiPullback (jComplex.comp κ) (f i)) = 0) :
    (∑ i ∈ I, c i • A.crystallinePullback (f i)) = 0 := by
  obtain ⟨hD, hC, cmp, phi, Fil, _hphi, _hFil, _hWA, hcr, _hWeil,
    ⟨localCmp, bettiCmp, hnatural, _hlocFil, _hbettiFil⟩, _hsummands⟩ := hcomparison
  exact betti_relation_implies_crystalline A (jComplex.comp κ) cmp localCmp bettiCmp
    (fun f => (hcr f).1) (fun f => (hnatural f).1) (fun f => (hnatural f).2) I f c h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonRelations.CM
