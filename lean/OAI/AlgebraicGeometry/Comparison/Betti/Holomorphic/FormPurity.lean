import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicSections

/-! # Form Purity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormPurity.Smooth

noncomputable section

/-! The actual realization of every algebraic n-form has geometric Hodge type (n,0). -/

open scoped _root_.Manifold ContDiff

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))
  (hc : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (φ a))

include hc in
theorem smoothSymbol_pure : ∀ (n : ℕ) (a : Fin (n + 1) → A),
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0 (HigherSmoothSymbols.smoothSymbol φ hφ n a).val := by
  intro n
  induction n with
  | zero =>
      intro a e he y hy
      exact Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero (E := E) _
  | succ n ih =>
      intro a
      rw [HigherSmoothSymbols.smoothSymbol_succ]
      exact AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.hasManifoldBidegree_wedge (ih (Fin.init a))
        (HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.regularDifferential_pure φ hφ hc _)

include hc in
theorem smoothFormMap_pure (n : ℕ) (a : Algebraic.Forms.Form A n) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0 (Smooth.CochainMap.smoothFormMap φ hφ n a).val := by
  have hsymbol (b : Fin (n + 1) → A) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0
      (Smooth.CochainMap.smoothFormMap φ hφ n (Algebraic.Forms.formSymbol A b)).val := by
    rw [Smooth.CochainMap.smoothFormMap_symbol]
    exact smoothSymbol_pure φ hφ hc n b
  obtain ⟨r, rfl⟩ := (Algebraic.Forms.relations A n).mkQ_surjective a
  induction r using Finsupp.induction_linear with
  | zero =>
      simp only [map_zero]
      exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.zero
  | add r t hr ht =>
      simp only [map_add]
      exact hr.add ht
  | single b c =>
      have he : Finsupp.single b c = c • Algebraic.Forms.symbol A b := by
        simp [Algebraic.Forms.symbol]
      rw [he]
      simp only [map_smul]
      exact (hsymbol b).const_smul c

def pureSmoothFormMap (n : ℕ) : Algebraic.Forms.Form A n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M n 0 :=
  (Smooth.CochainMap.smoothFormMap φ hφ n).codRestrict (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M n 0)
    (smoothFormMap_pure φ hφ hc n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormPurity.Smooth
