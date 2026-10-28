import OAI.NumberTheory.PadicHodge.ExtremeSlopesGeometricForced
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SameTestProjector

/-! # Character Purity Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterPurityTransport.Comparison

noncomputable section

/-! Transport full ExtremeSlopes character purity through the actual Betti
comparison to the rational weight-one Hodge structure. -/

open OAI.NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric

theorem character_purity_hodge_types
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
    {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
    (κ : K →+* AlgebraicClosure ℚ) (j : AlgebraicClosure ℚ →+* ℂ)
    {Hecke : Type} [CommRing Hecke] [Algebra ℚ Hecke]
    (ρ : A.HeckeRealization Hecke)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (j.comp κ)).scheme.left
      (A.complexFiber (j.comp κ)).scheme.hom)
    (χ : Hecke →ₐ[ℚ] AlgebraicClosure ℚ)
    (slope : Gal(AlgebraicClosure ℚ/ℚ) → ℚ)
    (hpurity : NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity A κ j ρ P χ slope)
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (e : ComplexMultiplication.WeightOne.CM.Complexification V ≃ₗ[ℂ] A.ComplexBetti (j.comp κ))
    (hF : H.holomorphic.map e.toLinearMap = A.bettiFiltration (j.comp κ) P 1)
    (σ : Gal(AlgebraicClosure ℚ/ℚ)) (Q : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (hQ : Q ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H)
    (hRange : LinearMap.range (e.conj Q) =
      A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (σ (χ h))))
    (hne : A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (σ (χ h))) ≠ ⊥) :
    (slope σ = 1 → LinearMap.range Q ≤ H.holomorphic) ∧
    (slope σ = 0 → LinearMap.range Q ≤ H.antiholomorphic) := by
  let B := H.antiholomorphic.map e.toLinearMap
  have hcompl : IsCompl (A.bettiFiltration (j.comp κ) P 1) B := by
    rw [← hF]
    exact IsCompl.map (Submodule.orderIsoMapComap e) H.complementary
  have hpres₁ : ∀ x ∈ A.bettiFiltration (j.comp κ) P 1,
      (e.conj Q) x ∈ A.bettiFiltration (j.comp κ) P 1 := by
    rw [← hF]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Q x, hQ.1 x hx, by simp⟩
  have hpres₂ : ∀ x ∈ B, (e.conj Q) x ∈ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Q x, hQ.2 x hx, by simp⟩
  have hp := hpurity σ B hcompl (e.conj Q) hRange hpres₁ hpres₂ hne
  have hmem {x : ComplexMultiplication.WeightOne.CM.Complexification V} (hx : x ∈ LinearMap.range Q) :
      e x ∈ A.bettiHeckeSummand (j.comp κ) ρ (fun h => j (σ (χ h))) := by
    rw [← hRange]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨e y, by simp⟩
  constructor
  · intro hs x hx
    have hm := hp.2.1.mp hs (hmem hx)
    rw [← hF] at hm
    obtain ⟨y, hy, he⟩ := hm
    exact e.injective he ▸ hy
  · intro hs x hx
    obtain ⟨y, hy, he⟩ := hp.2.2.mp hs (hmem hx)
    exact e.injective he ▸ hy

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterPurityTransport.Comparison
