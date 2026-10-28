import Mathlib

/-! # Pushout -/

namespace OAI.Topology.Pontryagin.Pushout.Constructions.CharacterExtension

noncomputable section

/-! CharacterExtension: the closed relation subgroup for the pushout of a character. -/

open Set _root_.Topology

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The relation identifies each `h ∈ H` with the circle element `χ h`. -/
def characterRelationHom (H : Subgroup G) (χ : H →ₜ* Circle) : H →* G × Circle where
  toFun h := ((h : G), (χ h)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    ext <;> simp [mul_comm]

def characterRelation (H : Subgroup G) (χ : H →ₜ* Circle) : Subgroup (G × Circle) :=
  (characterRelationHom H χ).range

lemma characterRelation_closed (H : Subgroup G) (hH : IsClosed (H : Set G))
    (χ : H →ₜ* Circle) : IsClosed (characterRelation H χ : Set (G × Circle)) := by
  have hclosed : IsClosed {p : H × Circle | (χ p.1)⁻¹ = p.2} :=
    isClosed_eq (χ.continuous.comp continuous_fst).inv continuous_snd
  have he : IsClosedEmbedding (fun p : H × Circle => ((p.1 : G), p.2)) :=
    (show IsClosedEmbedding ((↑) : H → G) from
      ⟨IsEmbedding.subtypeVal, by simpa using hH⟩).prodMap IsClosedEmbedding.id
  have himage : (fun p : H × Circle => ((p.1 : G), p.2)) ''
      {p : H × Circle | (χ p.1)⁻¹ = p.2} =
      (characterRelation H χ : Set (G × Circle)) := by
    ext p
    constructor
    · rintro ⟨⟨h, z⟩, hz, hp⟩
      refine ⟨h, ?_⟩
      change ((h : G), (χ h)⁻¹) = p
      change (χ h)⁻¹ = z at hz
      rw [hz]
      exact hp
    · rintro ⟨h, rfl⟩
      exact ⟨(h, (χ h)⁻¹), rfl, rfl⟩
  rw [← himage]
  exact he.isClosedMap _ hclosed

/-- The canonical continuous quotient map. -/
def characterQuotientMap (H : Subgroup G) (χ : H →ₜ* Circle) :
    (G × Circle) →ₜ* (G × Circle) ⧸ characterRelation H χ :=
  { QuotientGroup.mk' (characterRelation H χ) with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The circle embeds algebraically into the pushout. -/
def characterCircleMap (H : Subgroup G) (χ : H →ₜ* Circle) :
    Circle →ₜ* (G × Circle) ⧸ characterRelation H χ where
  toFun z := characterQuotientMap H χ (1, z)
  map_one' := by exact (characterQuotientMap H χ).map_one
  map_mul' a b := by simpa using (characterQuotientMap H χ).map_mul (1, a) (1, b)
  continuous_toFun := (characterQuotientMap H χ).continuous.comp
    (continuous_const.prodMk continuous_id)

lemma characterCircleMap_injective (H : Subgroup G) (χ : H →ₜ* Circle) :
    Function.Injective (characterCircleMap H χ) := by
  apply (injective_iff_map_eq_one (characterCircleMap H χ)).mpr
  intro z hz
  have hmem : (1, z) ∈ characterRelation H χ :=
    (QuotientGroup.eq_one_iff (1, z)).mp hz
  obtain ⟨h, hh⟩ := hmem
  have hh1 : h = 1 := Subtype.ext (congrArg Prod.fst hh)
  have hz1 := congrArg Prod.snd hh
  simpa [characterRelationHom, hh1] using hz1.symm

/-- In the pushout, `(h,1)` and `(1,χ h)` have the same image. -/
lemma characterQuotientMap_subgroup (H : Subgroup G) (χ : H →ₜ* Circle) (h : H) :
    characterQuotientMap H χ ((h : G), 1) = characterCircleMap H χ (χ h) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  refine ⟨h, ?_⟩
  ext <;> simp [characterRelationHom]

end

end OAI.Topology.Pontryagin.Pushout.Constructions.CharacterExtension
