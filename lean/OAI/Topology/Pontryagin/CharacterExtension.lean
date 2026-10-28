import OAI.Topology.Pontryagin.Compact
import OAI.Topology.Pontryagin.Pushout
import OAI.Topology.Pontryagin.Separation
import Lean.Util.CollectAxioms

/-! # Character Extension -/

namespace OAI.Topology.Pontryagin.CharacterExtension.Constructions

noncomputable section

/-!
# CharacterExtension: Pontryagin character extension

Every continuous unitary character of a closed subgroup of a Hausdorff locally
compact abelian group extends to the whole group. The hypotheses and conclusion
match `Statements/CharacterExtension.lean`; that specification is not imported.

The proof forms the pushout `(G × Circle) / {(h, χ(h)⁻¹) | h ∈ H}`.
Closedness makes this a Hausdorff LCA group, and the circle injects into it.
Character separation and Stone–Weierstrass extend the identity character of that
circle; composing with `g ↦ [(g,1)]` yields the prescribed extension.

-/

/-- Pontryagin's extension theorem for closed subgroups of Hausdorff LCA groups. -/
theorem pontryagin_character_extension
    {G : Type*}
    [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G)
    (hH : IsClosed (H : Set G))
    (χ : H →ₜ* Circle) :
    ∃ χG : G →ₜ* Circle, ∀ h : H, χG (h : G) = χ h := by
  let Q := (G × Circle) ⧸ Pushout.Constructions.CharacterExtension.characterRelation H χ
  have : IsClosed (Pushout.Constructions.CharacterExtension.characterRelation H χ : Set (G × Circle)) :=
    Pushout.Constructions.CharacterExtension.characterRelation_closed H hH χ
  obtain ⟨η, hη⟩ := Compact.Constructions.CharacterExtension.compact_character_extension
    (G := Q) Separation.Constructions.CharacterExtension.characters_separate_points
    (Pushout.Constructions.CharacterExtension.characterCircleMap H χ) (Pushout.Constructions.CharacterExtension.characterCircleMap_injective H χ)
    (ContinuousMonoidHom.id Circle)
  let j : G →ₜ* Q :=
    { toFun := fun g => Pushout.Constructions.CharacterExtension.characterQuotientMap H χ (g, 1)
      map_one' := (Pushout.Constructions.CharacterExtension.characterQuotientMap H χ).map_one
      map_mul' := fun a b => by
        simpa using (Pushout.Constructions.CharacterExtension.characterQuotientMap H χ).map_mul (a, 1) (b, 1)
      continuous_toFun := (Pushout.Constructions.CharacterExtension.characterQuotientMap H χ).continuous.comp
        (continuous_id.prodMk continuous_const) }
  refine ⟨(η : Q →ₜ* Circle).comp j, ?_⟩
  intro h
  change η (Pushout.Constructions.CharacterExtension.characterQuotientMap H χ ((h : G), 1)) = χ h
  rw [Pushout.Constructions.CharacterExtension.characterQuotientMap_subgroup]
  exact hη (χ h)

end

end OAI.Topology.Pontryagin.CharacterExtension.Constructions
