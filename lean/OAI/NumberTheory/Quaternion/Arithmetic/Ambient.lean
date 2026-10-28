import OAI.NumberTheory.Quaternion.Arithmetic.Groups
import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact
import OAI.NumberTheory.Quaternion.Arithmetic.NondiscreteProjection
import OAI.NumberTheory.Quaternion.Arithmetic.LocalClosure

/-! # Ambient -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Ambient

noncomputable section

/-! The actual arithmetic subgroup in the product of omitted and selected
local factors. These constructions connect the general quotient-volume
lemmas to the arithmetic groups in Arithmetic. -/

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
variable (S : Finset (LocalAdeles.Place F)) (T : Finset (ApproximationTopology.AwayPlace S))

abbrev OmittedLocalProduct := (v : (S : Set (LocalAdeles.Place F))) → LocalAdeles.LocalPoints G v.val

def arithmeticOmittedProjection : Groups.arithmeticSubgroup G S T →* OmittedLocalProduct G S where
  toFun g v := LocalAdeles.diagonalLocal G v.val g.val
  map_one' := by funext v; exact map_one (LocalAdeles.diagonalLocal G v.val)
  map_mul' g h := by funext v; exact map_mul (LocalAdeles.diagonalLocal G v.val) g.val h.val

def arithmeticAmbientEmbedding : Groups.arithmeticSubgroup G S T →*
    OmittedLocalProduct G S × Groups.SelectedLocalProduct G S T :=
  (arithmeticOmittedProjection G S T).prod (Groups.arithmeticProjection G S T)

def arithmeticAmbientSubgroup :
    Subgroup (OmittedLocalProduct G S × Groups.SelectedLocalProduct G S T) :=
  (arithmeticAmbientEmbedding G S T).range

theorem arithmeticAmbient_projection :
    (arithmeticAmbientSubgroup G S T).map
      (MonoidHom.snd (OmittedLocalProduct G S) (Groups.SelectedLocalProduct G S T)) =
      (Groups.arithmeticProjection G S T).range := by
  rw [arithmeticAmbientSubgroup, MonoidHom.map_range]
  rfl

theorem arithmeticProjection_injective (hT : T.Nonempty) :
    Function.Injective (Groups.arithmeticProjection G S T) := by
  obtain ⟨v, hv⟩ := hT
  intro g h hgh
  apply Subtype.ext
  apply LocalAdeles.diagonalLocal_injective G v.val
  exact congrFun hgh ⟨v, hv⟩

theorem arithmeticAmbient_snd_injective (hT : T.Nonempty) :
    Function.Injective
      ((MonoidHom.snd (OmittedLocalProduct G S) (Groups.SelectedLocalProduct G S T)).comp
        (arithmeticAmbientSubgroup G S T).subtype) := by
  intro g h hgh
  obtain ⟨a, ha⟩ := g.property
  obtain ⟨b, hb⟩ := h.property
  have hab : Groups.arithmeticProjection G S T a = Groups.arithmeticProjection G S T b := by
    change (arithmeticAmbientEmbedding G S T a).2 = (arithmeticAmbientEmbedding G S T b).2
    rw [ha, hb]
    exact hgh
  have := arithmeticProjection_injective G S T hT hab
  apply Subtype.ext
  rw [← ha, ← hb, this]

/-- The lattice-volume obligation alone gives nondiscreteness in every
nonempty selected product, under the original local noncompactness condition. -/
theorem arithmeticProjection_not_discrete (hT : T.Nonempty)
    (hnoncompact : ∃ v : LocalAdeles.Place F, v ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G v))
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability (arithmeticAmbientSubgroup G S T)) :
    ¬ IsDiscrete ((Groups.arithmeticProjection G S T).range : Set (Groups.SelectedLocalProduct G S T)) := by
  let : NoncompactSpace (OmittedLocalProduct G S) := not_compactSpace_iff.mp
    ((LocalAdeles.noncompact_place_iff_noncompact_product G S).mp hnoncompact)
  have h := NondiscreteProjection.projected_subgroup_not_discrete (arithmeticAmbientSubgroup G S T)
    (arithmeticAmbient_snd_injective G S T hT) hvolume
  rwa [arithmeticAmbient_projection] at h

/-- An open local closure has finite index once the arithmetic quotient
has finite invariant volume. -/
theorem arithmeticProjection_closure_finiteIndex
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability (arithmeticAmbientSubgroup G S T))
    (hopen : IsOpen ((Groups.arithmeticProjection G S T).range.topologicalClosure :
      Set (Groups.SelectedLocalProduct G S T))) :
    (Groups.arithmeticProjection G S T).range.topologicalClosure.FiniteIndex := by
  have hopen' : IsOpen
      (((arithmeticAmbientSubgroup G S T).map
        (MonoidHom.snd (OmittedLocalProduct G S) (Groups.SelectedLocalProduct G S T))).topologicalClosure :
          Set (Groups.SelectedLocalProduct G S T)) := by
    rwa [arithmeticAmbient_projection]
  have h := CompactQuotientProjection.projectedClosure_finiteIndex
    (MonoidHom.snd (OmittedLocalProduct G S) (Groups.SelectedLocalProduct G S T)) continuous_snd
    (fun x => ⟨(1, x), rfl⟩) (arithmeticAmbientSubgroup G S T) hvolume hopen'
  rwa [arithmeticAmbient_projection] at h

end

end OAI.NumberTheory.Quaternion.Arithmetic.Ambient
