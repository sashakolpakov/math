import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassMap

/-! # Top Class Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassCoefficients

noncomputable section

/-! Exact coefficient change preserves the actual full-intersection
class map, including its original cohomology comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G] [G.PreservesHomology]
  (P : Cᵒᵖ ⥤ A) (m : ℕ) (hm : Fintype.card ι = m)

omit [Abelian A] [Abelian B] [G.Additive] [G.PreservesHomology] in
theorem inclusion :
    G.map (AugmentedOrdered.CechCoordinates.topInclusion U P m hm) ≫
      (CoefficientChange.objectIso U G P m).hom =
    AugmentedOrdered.CechCoordinates.topInclusion U (P ⋙ G) m hm := by
  apply Pi.hom_ext
  intro a
  rw [Category.assoc]
  change G.map (AugmentedOrdered.CechCoordinates.topInclusion U P m hm) ≫ piComparison G _ ≫ _ = _
  erw [piComparison_comp_π, ← G.map_comp, AugmentedOrdered.CechCoordinates.topInclusion_comp_pi, AugmentedOrdered.CechCoordinates.topInclusion_comp_pi]
  rfl

def homologyIso : G.obj ((AugmentedOrdered.Cech.complex U P).homology m) ≅ (AugmentedOrdered.Cech.complex U (P ⋙ G)).homology m :=
  (((AugmentedOrdered.Cech.complex U P).sc m).mapHomologyIso G).symm ≪≫
    homologyMapIso (CoefficientChange.complexIso U G P) m

theorem comparison :
    G.map (TopClassMap.map U P m hm) ≫ (homologyIso U G P m).hom =
      TopClassMap.map U (P ⋙ G) m hm := by
  let K := AugmentedOrdered.Cech.complex U P
  let L := (G.mapHomologicalComplex (.up ℕ)).obj K
  let T := AugmentedOrdered.Cech.complex U (P ⋙ G)
  let e := CoefficientChange.complexIso U G P
  have hK : (K.sc m).g = 0 := TopClassMap.outgoing U P m hm
  have hL : (L.sc m).g = 0 := by
    change G.map (K.sc m).g = 0
    rw [hK, G.map_zero]
  have hT : (T.sc m).g = 0 := TopClassMap.outgoing U (P ⋙ G) m hm
  have hs : G.map (TopHomologyCokernel.shortClass (K.sc m) hK) ≫ ((K.sc m).mapHomologyIso G).inv =
      TopHomologyCokernel.shortClass (L.sc m) hL := by
    rw [← TopCycleBaseChange.shortClass_map G (K.sc m) hK hL,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have he : TopHomologyCokernel.shortClass (L.sc m) hL ≫ homologyMap e.hom m =
      e.hom.f m ≫ TopHomologyCokernel.shortClass (T.sc m) hT := by
    apply (cancel_mono (TopHomologyCokernel.shortIso (T.sc m) hT).hom).mp
    erw [Category.assoc, TopHomologyCokernel.short_naturality
      ((shortComplexFunctor B (.up ℕ) m).map e.hom) hL hT,
      ← Category.assoc, TopHomologyCokernel.shortClass_iso (L.sc m) hL,
      Category.assoc, TopHomologyCokernel.shortClass_iso (T.sc m) hT, cokernel.π_desc]
    rfl
  change G.map (AugmentedOrdered.CechCoordinates.topInclusion U P m hm ≫ TopHomologyCokernel.shortClass (K.sc m) hK) ≫
    (((K.sc m).mapHomologyIso G).inv ≫ homologyMap e.hom m) =
      AugmentedOrdered.CechCoordinates.topInclusion U (P ⋙ G) m hm ≫ TopHomologyCokernel.shortClass (T.sc m) hT
  rw [G.map_comp, Category.assoc, ← Category.assoc (G.map (TopHomologyCokernel.shortClass (K.sc m) hK)), hs,
    he, ← Category.assoc]
  exact congrArg (fun a => a ≫ TopHomologyCokernel.shortClass (T.sc m) hT) (inclusion U G P m hm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopClassCoefficients
