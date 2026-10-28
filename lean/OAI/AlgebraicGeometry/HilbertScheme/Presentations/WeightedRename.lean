import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerElimination

/-! # Weighted Rename -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedRename.GradedHilbert

noncomputable section

/-! Change of variables for weighted homogeneity, support, and ideal generation. -/

open _root_.MvPolynomial

variable {σ τ : Type*} {K : Type*} [Field K]

theorem naturalWeight_mapDomain (w : τ → ℕ) (f : σ → τ) (a : σ →₀ ℕ) :
    Finsupp.weight w (a.mapDomain f) = Finsupp.weight (w ∘ f) a := by
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · intro i
    exact zero_smul _ _
  · intro i x y
    exact add_smul x y (w i)

theorem weightedHomogeneous_rename (w : τ → ℕ) (f : σ → τ)
    {p : MvPolynomial σ K} {d : ℕ} (hp : p.IsWeightedHomogeneous (w ∘ f) d) :
    (rename f p).IsWeightedHomogeneous w d := by
  intro a ha
  obtain ⟨c, rfl, hc⟩ := coeff_rename_ne_zero f p a ha
  rw [naturalWeight_mapDomain]
  exact hp hc

theorem supported_rename_equiv (e : σ ≃ τ) (s : Set σ) (p : MvPolynomial σ K) :
    rename e p ∈ supported K (e '' s) ↔ p ∈ supported K s := by
  rw [mem_supported, mem_supported]
  constructor
  · intro hp i hi
    have hin : i ∈ (rename e.symm (rename e p)).vars := by
      simpa only [rename_rename, Equiv.symm_comp_self, rename_id, AlgHom.id_apply, Finset.mem_coe] using hi
    obtain ⟨j, hj, hji⟩ := mem_vars_rename e.symm (rename e p) hin
    obtain ⟨k, hk, hkj⟩ := hp hj
    have hki : k = i := by simpa only [← hkj, Equiv.symm_apply_apply] using hji
    exact hki ▸ hk
  · intro hp j hj
    obtain ⟨i, hi, rfl⟩ := mem_vars_rename e p hj
    exact ⟨i, hp hi, rfl⟩

theorem algEquiv_mem_span_image {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (s : Set A) (x : A) :
    e x ∈ Ideal.span (e '' s) ↔ x ∈ Ideal.span s := by
  rw [← Ideal.map_span]
  change e.toRingHom x ∈ Ideal.map e.toRingHom (Ideal.span s) ↔ x ∈ Ideal.span s
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact e.injective hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedRename.GradedHilbert
