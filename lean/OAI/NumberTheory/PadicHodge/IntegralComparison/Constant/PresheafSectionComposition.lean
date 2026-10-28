import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction

/-! # Presheaf Section Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.PresheafSectionComposition

noncomputable section

/-! The original constant-module section map is natural under maps of sheaf complexes. -/

open _root_.CategoryTheory

universe u v z

variable {C : Type u} [Category.{v} C] (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{u} R)]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (D : CochainComplex (ModuleCat.{u} R) ℕ)
  {K L : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ}
  (a : ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj D ⟶ K)
  (b : K ⟶ L)

theorem component (i : ℕ) :
    (ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D K a).f i ≫
      (IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u, v, u, z} R J).map (b.f i) =
    (ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D L (a ≫ b)).f i :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (ConstantSection.ComplexMap.map.{u, v, u, z} R J D K a).f i ≫ t)
      ((Ext.ZeroPresheafSections.iso.{u, v, u, z} R J).hom.naturality (b.f i)).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R J L).hom.f i)
            (ConstantSection.ComplexComposition.component.{u, v, u, z} R J D a b i).symm)))

theorem map : ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D K a ≫
    ((IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u, v, u, z} R J).mapHomologicalComplex (.up ℕ)).map b =
      ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D L (a ≫ b) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component R J D a b i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.PresheafSectionComposition
