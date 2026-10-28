import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSectionProjectors

/-! # Character Sheaf Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafSections

noncomputable section

/-! Every actual constant-torsor character sheaf has a constructed free rank-one section module over every base open in the tame case. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {S : Scheme.{u}} (c : K →+* Γ(S, ⊤))
    (G : Type u) [CommGroup G] [Fintype G]

def constantCharacterSheaf (χ : G →* Kˣ) : S.Modules :=
  IdempotentSheafSummands.idempotentSheafSummand
    (Sheaf.CharacterAverages.sheafCharacterAverage c (StructureRepresentation.constantStructurePushforward S G) (StructureRepresentation.constantStructureRepresentation S G) χ)

def constantCharacterSheafSectionsEquiv [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (χ : G →* Kˣ) (hG : (Fintype.card G : K) ≠ 0) (U : S.Opens) :
    Γ(constantCharacterSheaf c G χ, U) ≃ₗ[Γ(S, U)] Γ(S, U) :=
  IdempotentSheafSectionRanges.idempotentSheafSectionRangeEquiv _ (Sheaf.CharacterAverages.sheafCharacterAverage_idempotent c _ _ χ hG) U ≪≫ₗ
    LinearEquiv.ofEq _ _ (congrArg LinearMap.range (CharacterSectionProjectors.constantCharacterSectionProjector_eq c G U χ hG)) ≪≫ₗ
      Linear.ConjugateRanges.linearConjugateRangeEquiv (StructureSectionEquivalence.constantStructureSectionEquiv S G U) (CharacterSectionProjectors.openRegularCharacterProjector c G U χ) ≪≫ₗ
        CharacterSectionProjectors.openRegularCharacterProjectorRangeEquiv c G U χ

theorem constantCharacterSheafSections_finite_free [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (χ : G →* Kˣ) (hG : (Fintype.card G : K) ≠ 0) (U : S.Opens) :
    Module.Finite Γ(S, U) Γ(constantCharacterSheaf c G χ, U) ∧
      Module.Free Γ(S, U) Γ(constantCharacterSheaf c G χ, U) :=
  ⟨Module.Finite.equiv (constantCharacterSheafSectionsEquiv c G χ hG U).symm,
    Module.Free.of_equiv (constantCharacterSheafSectionsEquiv c G χ hG U).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafSections
