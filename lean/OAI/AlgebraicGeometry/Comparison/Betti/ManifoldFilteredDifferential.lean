import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFormFiltration
import OAI.Analysis.HodgeTheory.Decomposition.Dolbeault

/-! # Manifold Filtered Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFilteredDifferential.Hodge

noncomputable section

/-! The actual exterior derivative preserves the smooth Hodge filtration,
by its two genuine Dolbeault components. -/

open scoped _root_.Manifold ContDiff

open OAI.Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem castDegree_pureFormsInDegree (p q n : ℕ) (h : p + q = n)
    (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h a.val ∈ ManifoldFormFiltration.Hodge.pureFormsInDegree E M n ⟨(p, q), h⟩ := by
  cases h
  exact a.property

theorem manifoldDerivative_pure_decomposition (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (ha : a ∈ ManifoldFormFiltration.Hodge.pureFormsInDegree E M n i) :
    ∃ b c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (n + 1),
      b ∈ ManifoldFormFiltration.Hodge.pureFormsInDegree E M (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceHolomorphic i) ∧
      c ∈ ManifoldFormFiltration.Hodge.pureFormsInDegree E M (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i) ∧
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = b + c := by
  rcases i with ⟨⟨p, q⟩, hi⟩
  subst n
  let f : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q := ⟨a, ha⟩
  refine ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : (p + 1) + q = p + q + 1)
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime f).val,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : p + (q + 1) = p + q + 1)
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime f).val, ?_, ?_, ?_⟩
  · exact castDegree_pureFormsInDegree E M (p + 1) q (p + q + 1) _ _
  · exact castDegree_pureFormsInDegree E M p (q + 1) (p + q + 1) _ _
  · exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime f).symm

theorem manifoldExteriorDerivative_filtered (n : ℕ) (r : ℤ) :
    (ManifoldFormFiltration.Hodge.manifoldFormFiltration E M n r).map Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d ≤
      ManifoldFormFiltration.Hodge.manifoldFormFiltration E M (n + 1) r := by
  rw [Submodule.map_le_iff_le_comap]
  refine iSup_le fun i => iSup_le fun hri => ?_
  intro a ha
  obtain ⟨b, c, hb, hc, hd⟩ := manifoldDerivative_pure_decomposition E M n i a ha
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration E M (n + 1) r
  rw [hd]
  apply Submodule.add_mem
  · apply Submodule.mem_iSup_of_mem (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceHolomorphic i)
    apply Submodule.mem_iSup_of_mem (show r ≤ ((Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceHolomorphic i).val.1 : ℤ) by
      dsimp [Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceHolomorphic]
      omega)
    exact hb
  · apply Submodule.mem_iSup_of_mem (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i)
    apply Submodule.mem_iSup_of_mem (show r ≤ ((Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i).val.1 : ℤ) from hri)
    exact hc

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldFilteredDifferential.Hodge
