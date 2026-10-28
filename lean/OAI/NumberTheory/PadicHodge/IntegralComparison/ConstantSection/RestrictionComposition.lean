import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.PulledComposition

/-! # Restriction Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.RestrictionComposition

noncomputable section

/-! The original presheaf section comparison restricts after postcomposition. -/

open _root_.CategoryTheory

universe u v z

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [HasSheafify J (ModuleCat.{u} R)] [HasSheafify K (ModuleCat.{u} R)]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{u} R, F.op.HasPointwiseRightKanExtension P]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  [HasExt.{max u z} (Sheaf K (ModuleCat.{u} R))]
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  {N L : CochainComplex (Sheaf K (ModuleCat.{u} R)) ℕ}
  (a : ((constantSheaf K (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj M ⟶ N)
  (b : N ⟶ L)

theorem map : ComplexRestriction.sectionMap.{u, v, z} R K M L (a ≫ b) ≫
    IntegralComparison.Sheaf.PresheafSectionRestriction.complexMap F R J K L =
      ComplexMap.map R J M _
        (ComplexRestriction.pulled F R J K M N a ≫
          ((F.sheafPushforwardContinuous (ModuleCat.{u} R) J K).mapHomologicalComplex (.up ℕ)).map b) ≫
            (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R J _).hom :=
  (ComplexRestriction.naturality F R J K M L (a ≫ b)).trans
    (congrArg (fun c => ComplexMap.map R J M _ c ≫
      (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R J _).hom)
        (PulledComposition.map F R J K M a b))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.RestrictionComposition
