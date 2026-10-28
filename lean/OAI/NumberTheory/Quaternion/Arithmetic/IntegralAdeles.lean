import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact
import OAI.NumberTheory.Quaternion.Arithmetic.Groups

/-! # Integral Adeles -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralAdeles

noncomputable section

/-! Compact open integral subgroups of the away adeles. S-integral rational
points are exactly their inverse images under the diagonal homomorphism. -/

open scoped Classical _root_.NumberField RestrictedProduct
open Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))

def integralAwaySubgroup : Subgroup (LocalAdeles.AwayAdelicPoints G S) where
  carrier := {a | ∀ v, a v ∈ LocalAdeles.integralLocalSubgroup G v.val}
  one_mem' v := (LocalAdeles.integralLocalSubgroup G v.val).one_mem
  mul_mem' ha hb v := (LocalAdeles.integralLocalSubgroup G v.val).mul_mem (ha v) (hb v)
  inv_mem' ha v := (LocalAdeles.integralLocalSubgroup G v.val).inv_mem (ha v)

def integralAwayProductHomeomorph :
    ((v : ApproximationTopology.AwayPlace S) → LocalAdeles.integralLocalSubgroup G v.val) ≃ₜ integralAwaySubgroup G S :=
  (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : ApproximationTopology.AwayPlace S => LocalAdeles.LocalPoints G v.val)
    (A := fun v => (LocalAdeles.integralLocalSubgroup G v.val : Set (LocalAdeles.LocalPoints G v.val)))
    (𝓕 := Filter.cofinite)).toHomeomorph.trans
      (Homeomorph.setCongr (by rw [RestrictedProduct.range_structureMap]; rfl))

theorem integralAwaySubgroup_isOpen :
    IsOpen (integralAwaySubgroup G S : Set (LocalAdeles.AwayAdelicPoints G S)) := by
  have h := ApproximationTopology.basicAdelicSet_isOpen G S ∅ (fun _ => Set.univ) (by simp)
  simpa [ApproximationTopology.basicAdelicSet, integralAwaySubgroup] using h

theorem integralAwaySubgroup_isCompact
    (hS : ∀ v : NumberField.InfinitePlace F, Sum.inl v ∈ S) :
    IsCompact (integralAwaySubgroup G S : Set (LocalAdeles.AwayAdelicPoints G S)) := by
  let : ∀ v : ApproximationTopology.AwayPlace S, CompactSpace (LocalAdeles.integralLocalSubgroup G v.val) := fun v => by
    rcases v with ⟨v, hv⟩
    cases v with
    | inl w => exact (hv (hS w)).elim
    | inr w => exact isCompact_iff_compactSpace.mp (IntegralCompact.integralLocalSubgroup_isCompact G w)
  have : CompactSpace (integralAwaySubgroup G S) :=
    (integralAwayProductHomeomorph G S).compactSpace
  exact isCompact_iff_compactSpace.mpr this

theorem sIntegralPoints_eq_comap_integralAway :
    Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F)) =
      (integralAwaySubgroup G S).comap (LocalAdeles.diagonalAway G S) := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg v
    exact hg v.val v.property
  · intro hg v hv
    exact hg ⟨v, hv⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralAdeles
