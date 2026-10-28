import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedCone

/-! # Sheafified Sections Identity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSectionsIdentity

noncomputable section

/-! Literal coordinates for the balanced section map, established
degree by degree before transporting a quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u z
variable {C : Type u} [Category.{0} C] (R : Type u) [CommRing R]
  (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)
  (g : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ⟶ I.cocomplex)

theorem sectionsMap_eq :
    SheafifiedCone.Comparison.sectionsMap.{u,z} R J I M P a g =
    ConstantSection.ComplexMap.map.{u,0,u,z} R J M
      (Sheafified.ConstantCochainCoordinates.sheafComplex R J P)
      (Sheafified.ConstantCochainCoordinates.sheafMap R J M P a) ≫
      ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
        (.up ℕ)).map g := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem sourceComposite_eq :
    Sheafified.ConstantCochainCoordinates.sectionMap.{u,0,z} R J M P a ≫
      ResolutionHom.SourceNaturality.sectionsMap R g =
    SheafifiedCone.Comparison.sectionsMap.{u,z} R J I M P a g := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSectionsIdentity
