import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedRename

/-! # Variable Elimination -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.VariableElimination.GradedHilbert

noncomputable section

/-! Transport of bounded elimination to any finite collection of named variables. -/

open _root_.MvPolynomial

universe u v z

variable {K : Type u} [Field K] {σ : Type v} {n : ℕ}

theorem supported_complement_rename_equiv (e : σ ≃ Fin (n + 1))
    (s : Finset σ) (p : MvPolynomial σ K) :
    rename e p ∈ supported K (((s.image e : Finset (Fin (n + 1))) : Set (Fin (n + 1)))ᶜ) ↔
      p ∈ supported K ((s : Set σ)ᶜ) := by
  classical
  rw [Finset.coe_image, ← e.image_compl]
  exact WeightedRename.GradedHilbert.supported_rename_equiv e ((s : Set σ)ᶜ) p

theorem exists_weighted_elimination_generators_of_equiv
    (E : σ ≃ Fin (n + 1)) (w : σ → ℕ) (hw : ∀ i, w i ≠ 0)
    (s : Finset σ) {ι : Type z} [Fintype ι]
    (b : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous w (e i)) (hb0 : ∀ i, b i ≠ 0)
    (D : ℕ) (hD : ∀ i, e i ≤ D) :
    ∃ B : Finset (MvPolynomial σ K),
      (∀ g ∈ B, g ∈ Ideal.span (Set.range b) ∧ g ≠ 0 ∧
        g ∈ supported K ((s : Set σ)ᶜ) ∧
        ∃ d ≤ Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound n D, g.IsWeightedHomogeneous w d) ∧
      ∀ f ∈ supported K ((s : Set σ)ᶜ),
        f ∈ Ideal.span (Set.range b) ↔ f ∈ Ideal.span (B : Set (MvPolynomial σ K)) := by
  classical
  let A := renameEquiv K E
  let w' := w ∘ E.symm
  let b' : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n := fun i => A (b i)
  have hb' (i : ι) : (b' i).IsWeightedHomogeneous w' (e i) := by
    apply WeightedRename.GradedHilbert.weightedHomogeneous_rename w' E
    simpa only [w', Function.comp_def, Equiv.symm_apply_apply] using hb i
  have hb0' (i : ι) : b' i ≠ 0 := by
    intro hz
    exact hb0 i (A.injective (by simpa only [map_zero] using hz))
  obtain ⟨B', hB', hgen⟩ := GroebnerElimination.GradedHilbert.exists_uniform_weighted_elimination_generators w'
    (fun i => hw (E.symm i)) (s.image E) b' e hb' hb0' D hD
  let B := B'.image A.symm
  have hspan (p : MvPolynomial σ K) :
      A p ∈ Ideal.span (Set.range b') ↔ p ∈ Ideal.span (Set.range b) := by
    have h := WeightedRename.GradedHilbert.algEquiv_mem_span_image A.toRingEquiv (Set.range b) p
    change A p ∈ Ideal.span (A '' Set.range b) ↔ p ∈ Ideal.span (Set.range b) at h
    simpa only [← Set.range_comp, Function.comp_def, b'] using h
  have hs (p : MvPolynomial σ K) :
      A p ∈ supported K (((s.image E : Finset (Fin (n + 1))) : Set (Fin (n + 1)))ᶜ) ↔
      p ∈ supported K ((s : Set σ)ᶜ) := supported_complement_rename_equiv E s p
  have hBmem (g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hg : g ∈ B') :
      A.symm g ∈ Ideal.span (Set.range b) ∧ A.symm g ≠ 0 ∧
        A.symm g ∈ supported K ((s : Set σ)ᶜ) ∧
        ∃ d ≤ Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound n D,
          (A.symm g).IsWeightedHomogeneous w d := by
    obtain ⟨hgI, hg0, hgs, d, hd, hhom⟩ := hB' g hg
    refine ⟨(hspan _).mp (by simpa only [AlgEquiv.apply_symm_apply] using hgI),
      (fun hz => hg0 (A.symm.injective (by simpa only [map_zero] using hz))),
      (hs _).mp (by simpa only [AlgEquiv.apply_symm_apply] using hgs),
      d, hd, ?_⟩
    exact WeightedRename.GradedHilbert.weightedHomogeneous_rename w E.symm hhom
  refine ⟨B, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hg
    exact hBmem g' hg'
  · intro f hfs
    constructor
    · intro hf
      have hf' := (hgen (A f) ((hs f).mpr hfs)).mp ((hspan f).mpr hf)
      have h := (WeightedRename.GradedHilbert.algEquiv_mem_span_image A.symm.toRingEquiv
        (B' : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (A f)).mpr hf'
      change A.symm (A f) ∈ Ideal.span (A.symm '' (B' : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))) at h
      simpa only [AlgEquiv.symm_apply_apply, B, Finset.coe_image] using h
    · apply Ideal.span_le.mpr
      intro g hg
      obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hg
      exact (hBmem g' hg').1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.VariableElimination.GradedHilbert
