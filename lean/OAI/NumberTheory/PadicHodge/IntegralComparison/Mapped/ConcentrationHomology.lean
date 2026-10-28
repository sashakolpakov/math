import OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationHomologyNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleLeftHomology

/-! # Concentration Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.ConcentrationHomology

noncomputable section

/-! The original concentration inclusion, after an additive functor,
has the canonical surviving-homology coordinate. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) (c : ℕ)
  [F.PreservesLeftHomologyOf (K.sc c)]
  [F.PreservesLeftHomologyOf ((CohomologyConcentration.truncation K c).sc c)]
  [F.PreservesLeftHomologyOf (((single C (.up ℕ) c).obj (K.homology c)).sc c)]

theorem inclusion :
    homologyMap ((F.mapHomologicalComplex (.up ℕ)).map
        (CohomologyConcentration.inclusion K c)) c =
      homologyMap ((singleMapHomologicalComplex F (.up ℕ) c).hom.app (K.homology c)) c ≫
        (singleObjHomologySelfIso (.up ℕ) c (F.obj (K.homology c))).hom ≫
          ((K.sc c).mapHomologyIso F).inv ≫
            homologyMap ((F.mapHomologicalComplex (.up ℕ)).map (CohomologyConcentration.projection K c)) c := by
  have hp : homologyMap ((F.mapHomologicalComplex (.up ℕ)).map (CohomologyConcentration.projection K c)) c ≫
      (((CohomologyConcentration.truncation K c).sc c).mapHomologyIso F).hom =
        ((K.sc c).mapHomologyIso F).hom ≫ F.map (homologyMap (CohomologyConcentration.projection K c) c) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor C (.up ℕ) c).map (CohomologyConcentration.projection K c)) F
  have hi : homologyMap ((F.mapHomologicalComplex (.up ℕ)).map
        (CohomologyConcentration.inclusion K c)) c ≫
      (((CohomologyConcentration.truncation K c).sc c).mapHomologyIso F).hom =
        ((((single C (.up ℕ) c).obj (K.homology c)).sc c).mapHomologyIso F).hom ≫
          F.map (homologyMap (CohomologyConcentration.inclusion K c) c) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor C (.up ℕ) c).map (CohomologyConcentration.inclusion K c)) F
  apply (cancel_mono (((CohomologyConcentration.truncation K c).sc c).mapHomologyIso F).hom).mp
  simp only [Category.assoc]
  rw [hp, Iso.inv_hom_id_assoc, hi,
    ConcentrationHomologyNormalization.inclusion K c, F.map_comp]
  rw [← Category.assoc,
    ← SingleLeftHomology.single F (K.homology c) c, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.ConcentrationHomology
