import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseDualEvaluationFrames

/-! # Sparse Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SparseCoverage.StableHilbertCoverage

noncomputable section

/-! Strict subspace sparsity is invariant under the actual linear
coordinate changes, relabelings, and pointwise units used by stable charts. -/

open scoped Classical
universe u v w

theorem sparse_linearEquiv
    {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {ι : Type v} [Fintype ι]
    (r : ℕ) (a : ι → V)
    (ha : ∀ U : Submodule K V, U ≠ ⊤ →
      r * (Finset.univ.filter (fun i => a i ∈ U)).card < Fintype.card ι)
    (e : V ≃ₗ[K] W) (U : Submodule K W) (hU : U ≠ ⊤) :
    r * (Finset.univ.filter (fun i => e (a i) ∈ U)).card < Fintype.card ι := by
  apply ha (U.comap e.toLinearMap)
  intro h
  apply hU
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy : y ∈ U.comap e.toLinearMap := h.symm ▸ Submodule.mem_top
  exact hy

theorem sparse_reindex
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (r : ℕ) (a : ι → V)
    (ha : ∀ U : Submodule K V, U ≠ ⊤ →
      r * (Finset.univ.filter (fun i => a i ∈ U)).card < Fintype.card ι)
    (e : κ ≃ ι) (U : Submodule K V) (hU : U ≠ ⊤) :
    r * (Finset.univ.filter (fun i => a (e i) ∈ U)).card < Fintype.card κ := by
  have he : (Finset.univ.filter (fun i => a (e i) ∈ U)).card =
      (Finset.univ.filter (fun i => a i ∈ U)).card := by
    simpa only [Fintype.card_subtype] using
      Fintype.card_congr (e.subtypeEquivOfSubtype (p := fun i => a i ∈ U))
  rw [he, Fintype.card_congr e]
  exact ha U hU

theorem sparse_units_smul
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type v} [Fintype ι] (r : ℕ) (a : ι → V)
    (ha : ∀ U : Submodule K V, U ≠ ⊤ →
      r * (Finset.univ.filter (fun i => a i ∈ U)).card < Fintype.card ι)
    (z : ι → Kˣ) (U : Submodule K V) (hU : U ≠ ⊤) :
    r * (Finset.univ.filter (fun i => (z i : K) • a i ∈ U)).card < Fintype.card ι := by
  have he (i : ι) : (z i : K) • a i ∈ U ↔ a i ∈ U :=
    U.smul_mem_iff (Units.ne_zero (z i))
  simpa only [he] using ha U hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SparseCoverage.StableHilbertCoverage
