import OAI.NumberTheory.Quaternion.Arithmetic.ClosureCommensurability

/-! # Closure -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Closure

noncomputable section

/-! Rational conjugation preserves the germ at the identity of each local
arithmetic closure. This is proved from compact open integrality conditions,
without assuming the desired density. -/

open scoped Classical
open _root_.Topology

theorem commensurable_map_of_injective {A L : Type*} [Group A] [Group L]
    (f : A →* L) (hf : Function.Injective f) {H K : Subgroup A}
    (h : H.Commensurable K) : (H.map f).Commensurable (K.map f) := by
  constructor
  · refine ⟨?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact h.1.relIndex_ne_zero
  · refine ⟨?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ hf]
    exact h.2.relIndex_ne_zero

theorem map_comap_conj {A L : Type*} [Group A] [Group L]
    (f : A →* L) (H : Subgroup A) (g : A) :
    (H.comap (MulAut.conj g).toMonoidHom).map f =
      (H.map f).comap (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.comap_equiv_eq_map_symm',
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem closure_comap_conj {L : Type*} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] (H : Subgroup L) (g : L) :
    (H.comap (MulAut.conj g).toMonoidHom).topologicalClosure =
      H.topologicalClosure.comap (MulAut.conj g).toMonoidHom := by
  let e : L ≃ₜ L := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  apply SetLike.coe_injective
  change closure (e ⁻¹' (H : Set L)) = e ⁻¹' closure (H : Set L)
  exact (e.preimage_closure (H : Set L)).symm

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) (v : LocalAdeles.Place F)

def localArithmeticSubgroup : Subgroup (LocalAdeles.LocalPoints G v) :=
  (Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F))).map (LocalAdeles.diagonalLocal G v)

theorem localArithmetic_conjugate_commensurable
    (hS : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (g : G.RationalPoints) :
    ((localArithmeticSubgroup G S v).comap
      (MulAut.conj (LocalAdeles.diagonalLocal G v g)).toMonoidHom).Commensurable
        (localArithmeticSubgroup G S v) := by
  have h := commensurable_map_of_injective (LocalAdeles.diagonalLocal G v) (LocalAdeles.diagonalLocal_injective G v)
    (Commensurability.sIntegralPoints_conjugate_commensurable G S hS g)
  rwa [map_comap_conj] at h

theorem localArithmetic_conjugate_closures_agree_near_one
    (hS : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (g : G.RationalPoints) :
    ∀ᶠ x in 𝓝 (1 : LocalAdeles.LocalPoints G v),
      x ∈ ((localArithmeticSubgroup G S v).comap
        (MulAut.conj (LocalAdeles.diagonalLocal G v g)).toMonoidHom).topologicalClosure ↔
      x ∈ (localArithmeticSubgroup G S v).topologicalClosure :=
  ClosureCommensurability.commensurable_closures_eventually_mem_iff (localArithmetic_conjugate_commensurable G S v hS g)

/-- Conjugation by every rational point preserves the local arithmetic
closure in an ambient neighborhood of the identity. -/
theorem rational_conjugation_preserves_localArithmetic_germ
    (hS : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) (g : G.RationalPoints) :
    ∀ᶠ x in 𝓝 (1 : LocalAdeles.LocalPoints G v),
      LocalAdeles.diagonalLocal G v g * x * (LocalAdeles.diagonalLocal G v g)⁻¹ ∈
        (localArithmeticSubgroup G S v).topologicalClosure ↔
      x ∈ (localArithmeticSubgroup G S v).topologicalClosure := by
  have h := localArithmetic_conjugate_closures_agree_near_one G S v hS g
  rw [closure_comap_conj] at h
  exact h

end

end OAI.NumberTheory.Quaternion.Arithmetic.Closure
