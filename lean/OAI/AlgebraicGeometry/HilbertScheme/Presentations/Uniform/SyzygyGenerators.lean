import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygySubstitutionComparison
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPolynomialCoefficients

/-! # Syzygy Generators -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SyzygyGenerators.GradedHilbert

noncomputable section

/-! Uniform homogeneous generators for the actual relation module of finitely many homogeneous polynomials. -/

open _root_.MvPolynomial

universe u v z

variable {K : Type u} [Field K] {σ : Type v} {ι : Type z} [Fintype ι]

theorem exists_uniform_homogeneous_syzygy_generators
    {n : ℕ} (E : (ι ⊕ Option σ) ≃ Fin (n + 1))
    (g : ι → MvPolynomial σ K) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    ∃ B : Finset (ι → MvPolynomial σ K),
      LinearMap.ker (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g) =
        Submodule.span (MvPolynomial σ K) (B : Set (ι → MvPolynomial σ K)) ∧
      ∀ b ∈ B, ∃ d ≤ GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound n (N + 1),
        ∀ i, (b i).IsHomogeneous d := by
  classical
  obtain ⟨G, hG, hgen⟩ := SyzygyGraphEquations.GradedHilbert.exists_bounded_syzygy_graph_elimination E g N hg
  let A := sumAlgEquiv K ι σ
  let T : MvPolynomial (ι ⊕ Option σ) K →ₐ[K] MvPolynomial ι (MvPolynomial σ K) :=
    A.toAlgHom.comp SyzygyGraphProjection.GradedHilbert.syzygyGraphProjection
  let C := G.image T
  have hT (f : MvPolynomial (ι ⊕ σ) K) : T (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding f) = A f := by
    change A (SyzygyGraphProjection.GradedHilbert.syzygyGraphProjection (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding f)) = A f
    rw [SyzygyGraphProjection.GradedHilbert.syzygyGraphProjection_rename]
  have hker (q : MvPolynomial (ι ⊕ Option σ) K) (hq : q ∈ G) :
      Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g (T q) = 0 := by
    apply (SyzygySubstitutionComparison.GradedHilbert.syzygy_graph_kernel_comparison g (SyzygyGraphProjection.GradedHilbert.syzygyGraphProjection q)).mp
    rw [SyzygyGraphProjection.GradedHilbert.syzygy_rename_projection q (hG q hq).2.2.1]
    exact (hG q hq).1
  have hspan : RingHom.ker (Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g).toRingHom =
      Ideal.span (C : Set (MvPolynomial ι (MvPolynomial σ K))) := by
    apply le_antisymm
    · intro p hp
      have hp0 : Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g p = 0 := RingHom.mem_ker.mp hp
      let f := A.symm p
      have hf0 : GraphSubstitutionIdeal.GradedHilbert.graphSubstitution (SyzygyGraphEquations.GradedHilbert.syzygyGraphData g) (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding f) = 0 := by
        apply (SyzygySubstitutionComparison.GradedHilbert.syzygy_graph_kernel_comparison g f).mpr
        change Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g (A (A.symm p)) = 0
        simpa only [AlgEquiv.apply_symm_apply] using hp0
      have hmem := (hgen (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding f) (SyzygyGraphProjection.GradedHilbert.syzygy_rename_supported f)).mp hf0
      have hm := Ideal.mem_map_of_mem T.toRingHom hmem
      rw [Ideal.map_span] at hm
      change T (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding f) ∈ Ideal.span (T '' (G : Set _)) at hm
      rw [hT] at hm
      simpa only [f, AlgEquiv.apply_symm_apply, C, Finset.coe_image] using hm
    · apply Ideal.span_le.mpr
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact hker q hq
  let B := C.image Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart
  refine ⟨B, ?_, ?_⟩
  · have he := SyzygiesFromPolynomialKernel.GradedHilbert.syzygy_kernel_eq_span_linearParts g (C : Set _) hspan
    simpa only [B, Finset.coe_image] using he
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, hhom⟩ := (hG q hq).2.2.2
    refine ⟨d - (N + 1), (Nat.sub_le d (N + 1)).trans hd, ?_⟩
    intro i
    exact IteratedPolynomialCoefficients.GradedHilbert.iterated_linearPart_homogeneous (SyzygyGraphProjection.GradedHilbert.syzygyGraphProjection_weighted_homogeneous hhom) i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SyzygyGenerators.GradedHilbert
