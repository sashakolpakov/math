import OAI.NumberTheory.Quaternion.Arithmetic.IntegralAdeles

/-! # Commensurability -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Commensurability

noncomputable section

/-! Rational conjugation commensurates the actual S-integral arithmetic
subgroups. This follows from compact open adelic subgroups, independently
of strong approximation or an arithmetic finite-volume theorem. -/

open scoped Classical

theorem compact_open_subgroups_commensurable
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (H J : Subgroup K) (hHc : IsCompact (H : Set K)) (hHo : IsOpen (H : Set K))
    (hJc : IsCompact (J : Set K)) (hJo : IsOpen (J : Set K)) :
    H.Commensurable J := by
  constructor
  · let : CompactSpace J := isCompact_iff_compactSpace.mp hJc
    exact ⟨(IntegralCompact.finiteIndex_of_open_in_compact_group (H.subgroupOf J)
      (hHo.preimage continuous_subtype_val)).index_ne_zero⟩
  · let : CompactSpace H := isCompact_iff_compactSpace.mp hHc
    exact ⟨(IntegralCompact.finiteIndex_of_open_in_compact_group (J.subgroupOf H)
      (hJo.preimage continuous_subtype_val)).index_ne_zero⟩

theorem commensurable_comap {A K : Type*} [Group A] [Group K]
    (f : A →* K) {H J : Subgroup K} (h : H.Commensurable J) :
    (H.comap f).Commensurable (J.comap f) :=
  ⟨⟨Subgroup.relIndex_comap_ne_zero f h.1.relIndex_ne_zero⟩,
    ⟨Subgroup.relIndex_comap_ne_zero f h.2.relIndex_ne_zero⟩⟩

theorem compact_open_conjugate_commensurable
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (H : Subgroup K) (hc : IsCompact (H : Set K)) (ho : IsOpen (H : Set K)) (g : K) :
    (H.comap (MulAut.conj g).toMonoidHom).Commensurable H := by
  let e : K ≃ₜ K := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  apply compact_open_subgroups_commensurable _ H _ _ hc ho
  · exact e.isCompact_preimage.mpr hc
  · exact ho.preimage e.continuous

theorem comap_conjugate_commensurable
    {A K : Type*} [Group A] [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : A →* K) (H : Subgroup K) (hc : IsCompact (H : Set K))
    (ho : IsOpen (H : Set K)) (g : A) :
    ((H.comap f).comap (MulAut.conj g).toMonoidHom).Commensurable (H.comap f) := by
  have he : (H.comap f).comap (MulAut.conj g).toMonoidHom =
      (H.comap (MulAut.conj (f g)).toMonoidHom).comap f := by
    apply Subgroup.ext
    intro x
    change f (g * x * g⁻¹) ∈ H ↔ f g * f x * (f g)⁻¹ ∈ H
    rw [map_mul, map_mul, map_inv]
  rw [he]
  exact commensurable_comap f (compact_open_conjugate_commensurable H hc ho (f g))

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))

theorem sIntegralPoints_conjugate_commensurable
    (hS : ∀ v : NumberField.InfinitePlace F, Sum.inl v ∈ S) (g : G.RationalPoints) :
    ((Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F))).comap (MulAut.conj g).toMonoidHom).Commensurable
      (Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F))) := by
  rw [IntegralAdeles.sIntegralPoints_eq_comap_integralAway]
  exact comap_conjugate_commensurable (LocalAdeles.diagonalAway G S) (IntegralAdeles.integralAwaySubgroup G S)
    (IntegralAdeles.integralAwaySubgroup_isCompact G S hS) (IntegralAdeles.integralAwaySubgroup_isOpen G S) g

theorem arithmeticSubgroup_conjugate_commensurable
    (hS : ∀ v : NumberField.InfinitePlace F, Sum.inl v ∈ S)
    (T : Finset (ApproximationTopology.AwayPlace S)) (g : G.RationalPoints) :
    ((Groups.arithmeticSubgroup G S T).comap (MulAut.conj g).toMonoidHom).Commensurable
      (Groups.arithmeticSubgroup G S T) := by
  rw [Groups.arithmeticSubgroup_eq_sIntegralPoints]
  have he : ((S ∪ T.image Subtype.val : Finset (LocalAdeles.Place F)) : Set (LocalAdeles.Place F)) =
      (S : Set (LocalAdeles.Place F)) ∪ Subtype.val '' (T : Set (ApproximationTopology.AwayPlace S)) := by
    simp
  rw [← he]
  exact sIntegralPoints_conjugate_commensurable G _
    (fun v => Finset.mem_union_left _ (hS v)) g

end

end OAI.NumberTheory.Quaternion.Arithmetic.Commensurability
