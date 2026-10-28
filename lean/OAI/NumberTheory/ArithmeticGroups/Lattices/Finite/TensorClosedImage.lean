import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation

/-! # Tensor Closed Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.TensorClosedImage.Construction

noncomputable section

/-! A finite family of tensors in invariant closed discrete modules gives
a closed stabilizer image in the ambient arithmetic quotient. -/

open scoped Classical
open Set MulAction

theorem finite_tensor_set_discrete
    {J U D : Type*} [Finite J] [TopologicalSpace U] [TopologicalSpace D]
    (L : Set U) (M : Set D) (hL : IsDiscrete L) (hM : IsDiscrete M) :
    IsDiscrete ((Set.pi Set.univ (fun _ : J => L)) ×ˢ M) := by
  let : DiscreteTopology L := isDiscrete_iff_discreteTopology.mp hL
  let : DiscreteTopology M := isDiscrete_iff_discreteTopology.mp hM
  let S := (Set.pi Set.univ (fun _ : J => L)) ×ˢ M
  let f : S → (J → L) × M := fun z =>
    (fun j => ⟨z.val.1 j, z.property.1 j trivial⟩, ⟨z.val.2, z.property.2⟩)
  apply isDiscrete_iff_discreteTopology.mpr
  apply DiscreteTopology.of_continuous_injective (f := f)
  · apply Continuous.prodMk
    · apply continuous_pi
      intro j
      exact ((continuous_apply j).comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  · intro x y he
    apply Subtype.ext
    apply Prod.ext
    · funext j
      exact congrArg (fun z : (J → L) × M => (z.1 j).val) he
    · exact congrArg (fun z : (J → L) × M => z.2.val) he

theorem stabilizer_image_closed_of_finite_tensors
    {H J U D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Finite J] [TopologicalSpace U] [TopologicalSpace D]
    [MulAction H U] [MulAction H D] [ContinuousSMul H U] [ContinuousSMul H D]
    (Γ : Subgroup H) (x : J → U) (y : D)
    (L : Set U) (M : Set D) (hLc : IsClosed L) (hMc : IsClosed M)
    (hLd : IsDiscrete L) (hMd : IsDiscrete M)
    (hx : ∀ j, x j ∈ L) (hy : y ∈ M)
    (hLstable : ∀ g ∈ Γ, ∀ z ∈ L, g • z ∈ L)
    (hMstable : ∀ g ∈ Γ, ∀ z ∈ M, g • z ∈ M) :
    IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) ''
      (((⨅ j, stabilizer H (x j)) ⊓ stabilizer H y : Subgroup H) : Set H)) := by
  have hstab : (⨅ j, stabilizer H (x j)) ⊓ stabilizer H y = stabilizer H (x, y) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf, mem_stabilizer_iff]
    change ((∀ j, g • x j = x j) ∧ g • y = y) ↔ g • (x, y) = (x, y)
    constructor
    · rintro ⟨hx, hy⟩
      exact Prod.ext (funext hx) hy
    · intro h
      exact ⟨fun j => congrArg (fun z : (J → U) × D => z.1 j) h,
        congrArg Prod.snd h⟩
  rw [hstab]
  apply StabilizerSaturation.Construction.stabilizer_image_closed_of_discrete_invariant_set Γ (x, y)
    ((Set.pi Set.univ (fun _ : J => L)) ×ˢ M)
  · exact (isClosed_set_pi (fun _ _ => hLc)).prod hMc
  · exact finite_tensor_set_discrete L M hLd hMd
  · exact ⟨fun j _ => hx j, hy⟩
  · intro g hg z hz
    exact ⟨fun j _ => hLstable g hg (z.1 j) (hz.1 j trivial), hMstable g hg z.2 hz.2⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.TensorClosedImage.Construction
