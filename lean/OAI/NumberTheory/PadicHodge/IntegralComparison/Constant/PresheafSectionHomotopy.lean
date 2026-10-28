import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.PresheafSectionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Homotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPostcomposition

/-! # Presheaf Section Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.PresheafSectionHomotopy

noncomputable section

/-! Original presheaf section comparisons are independent of homotopic resolution maps. -/

open _root_.CategoryTheory

universe u v z

variable {C : Type u} [Category.{v} C] (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{u} R)]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (D : CochainComplex (ModuleCat.{u} R) ℕ)
  {K L M : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ}
  (a : ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj D ⟶ K)

theorem homology (b c : K ⟶ L) (h : Homotopy b c) (i : ℕ) :
    HomologicalComplex.homologyMap
      (ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D L (a ≫ b)) i =
    HomologicalComplex.homologyMap
      (ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D L (a ≫ c)) i :=
  HomologyMapPostcomposition.equality
    (ConstantSection.ComplexMap.map.{u, v, u, z} R J D L (a ≫ b))
    (ConstantSection.ComplexMap.map.{u, v, u, z} R J D L (a ≫ c))
    (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R J L).hom i
    (ConstantSection.Homotopy.homology R J D a b c h i)

theorem reassociate (b : K ⟶ L) (c : L ⟶ M) :
    ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D L (a ≫ b) ≫
      ((IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u, v, u, z} R J).mapHomologicalComplex (.up ℕ)).map c =
    ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D M (a ≫ b ≫ c) :=
  (PresheafSectionComposition.map R J D (a ≫ b) c).trans
    (congrArg (ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D M) (Category.assoc a b c))

theorem composition (b : K ⟶ L) (c : L ⟶ M) (d : K ⟶ M) (h : Homotopy (b ≫ c) d) (i : ℕ) :
    HomologicalComplex.homologyMap
      (ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D L (a ≫ b) ≫
        ((IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u, v, u, z} R J).mapHomologicalComplex (.up ℕ)).map c) i =
    HomologicalComplex.homologyMap
      (ConstantSection.ComplexRestriction.sectionMap.{u, v, z} R J D M (a ≫ d)) i :=
  (congrArg (fun t => HomologicalComplex.homologyMap t i) (reassociate R J D a b c)).trans
    (homology R J D a (b ≫ c) d h i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.PresheafSectionHomotopy
