import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.GeneratedImages

/-! # Generation Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GenerationCriterion

noncomputable section

/-! Surjectivity of the explicit normalized generation matrix detects equality of relation modules. -/

universe u v w

theorem submodule_sup_section_range_eq_top_iff {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W]
    (q : V →ₗ[R] W) (s : W →ₗ[R] V) (hs : q.comp s = LinearMap.id)
    (N : Submodule R V) (hN : N ≤ q.ker) :
    N ⊔ s.range = ⊤ ↔ N = q.ker := by
  constructor
  · intro h
    apply le_antisymm hN
    intro x hx
    have hmem : x ∈ N ⊔ s.range := h.symm ▸ Submodule.mem_top
    obtain ⟨n, hn, z, ⟨y, rfl⟩, he⟩ := Submodule.mem_sup.mp hmem
    have hn0 : q n = 0 := hN hn
    have hx0 : q x = 0 := hx
    have hy : y = 0 := by
      calc
        y = q (s y) := (LinearMap.congr_fun hs y).symm
        _ = q (n + s y) := by rw [map_add, hn0, zero_add]
        _ = q x := congrArg q he
        _ = 0 := hx0
    rw [hy, map_zero, add_zero] at he
    exact he ▸ hn
  · intro h
    rw [h]
    apply top_unique
    intro x _
    have hx : x - s (q x) ∈ q.ker := by
      change q (x - s (q x)) = 0
      have hqx : q (s (q x)) = q x := LinearMap.congr_fun hs (q x)
      rw [map_sub, hqx, sub_self]
    exact Submodule.mem_sup.mpr ⟨x - s (q x), hx, s (q x), ⟨q x, rfl⟩, sub_add_cancel _ _⟩

variable {R : Type u} [CommRing R] {ι ν κ μ α : Type v}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]

theorem normalizedGenerationMatrix_surjective_iff (a : ι → ν) (b : κ → μ)
    (Q : Matrix ι ν R) (K : Matrix κ μ R) (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized b K)
    (F : α → Matrix μ ν R)
    (hF : ∀ i, (Matrix.toLin' Q).ker ≤ ((Matrix.toLin' K).ker).comap (Matrix.toLin' (F i))) :
    Function.Surjective (Matrix.toLin' (HilbertConstruction.Matrix.GeneratedImages.normalizedGenerationMatrix a b Q F)) ↔
      (Matrix.toLin' K).ker = ⨆ i, ((Matrix.toLin' Q).ker).map (Matrix.toLin' (F i)) := by
  have hN : (⨆ i, ((Matrix.toLin' Q).ker).map (Matrix.toLin' (F i))) ≤ (Matrix.toLin' K).ker :=
    iSup_le (fun i => Submodule.map_le_iff_le_comap.mpr (hF i))
  rw [← LinearMap.range_eq_top, HilbertConstruction.Matrix.GeneratedImages.normalizedGenerationMatrix_range a b Q hQ F,
    submodule_sup_section_range_eq_top_iff (Matrix.toLin' K) (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap b)
      (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedMatrix_comp_selectedBasisMap b K hK) _ hN]
  exact eq_comm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GenerationCriterion
