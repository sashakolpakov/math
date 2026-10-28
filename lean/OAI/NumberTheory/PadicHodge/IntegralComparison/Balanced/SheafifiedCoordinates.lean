import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCone

/-! # Sheafified Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCoordinates.Comparison

noncomputable section

/-! The literal cohomology square of the sheafified balanced cone,
with its exact arrows fixed before any geometric specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u z
variable {C : Type u} [Category.{0} C] [HasBinaryProducts C]
  {ι : Type} [Finite ι] (F : ι → C) (R : Type u) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (hcover : ∀ V, CoveringObjectsSheafDetection.sieve F V ∈ J V)
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)
  (g : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ⟶ I.cocomplex)

attribute [local instance] SheafifiedCone.Comparison.coproducts
  SheafifiedCone.Comparison.smallLimits SheafifiedCone.Comparison.smallProducts

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates.sheafComplex R J P

theorem square :
    SheafifiedCone.Comparison.liftedMap.{u,z} F R J M P a ≫
      (FrameCech.IntrinsicTotalCoordinates.Intrinsic.totalIso.{u,0,z} F R J K).hom =
    ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
      (Sheafified.ConstantCechMap.map F R J M P a) :=
  SheafifiedCone.Comparison.square.{u,z} F R J M P a

omit [Finite ι] in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
        (SheafifiedCone.Comparison.liftedMap.{u,z} F R J M P a) i ≫
      FrameAugmentation.comparison F R J hcover I K g i =
    HomologicalComplex.homologyMap
        (SheafifiedCone.Comparison.sectionsMap.{u,z} R J I M P a g) i ≫
      (InjectiveSectionCohomology.homologyIso R
        (Ext.ZeroPresheafSections.constantUnit R J) I i).hom :=
  SheafifiedCone.Comparison.lifted_homology.{u,z} F R J hcover I M P a g i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCoordinates.Comparison
