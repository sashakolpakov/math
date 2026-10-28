import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientChange
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Coefficient Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientCohomology.Change

noncomputable section

/-! Coefficient change on the original augmented Čech cohomology is
natural in the coefficient diagram. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G] [G.PreservesHomology]
  (P : Cᵒᵖ ⥤ A)

def homologyIso (n : ℕ) : G.obj ((AugmentedOrdered.Cech.complex U P).homology n) ≅
    (AugmentedOrdered.Cech.complex U (P ⋙ G)).homology n :=
  (((AugmentedOrdered.Cech.complex U P).sc n).mapHomologyIso G).symm ≪≫
    homologyMapIso (CoefficientChange.complexIso U G P) n

@[reassoc]
theorem homology_naturality {Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    G.map (homologyMap (AugmentedOrdered.CechFunctor.complexMap U α) n) ≫ (homologyIso U G Q n).hom =
      (homologyIso U G P n).hom ≫
        homologyMap (AugmentedOrdered.CechFunctor.complexMap U (Functor.whiskerRight α G)) n := by
  have h := congrArg (fun a => homologyMap a n) (CoefficientChange.naturality U G P α)
  simp only [homologyMap_comp] at h
  have hG : G.map (homologyMap (AugmentedOrdered.CechFunctor.complexMap U α) n) ≫
        (((AugmentedOrdered.Cech.complex U Q).sc n).mapHomologyIso G).inv =
      (((AugmentedOrdered.Cech.complex U P).sc n).mapHomologyIso G).inv ≫
        homologyMap ((G.mapHomologicalComplex (.up ℕ)).map (AugmentedOrdered.CechFunctor.complexMap U α)) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((shortComplexFunctor A (.up ℕ) n).map (AugmentedOrdered.CechFunctor.complexMap U α)) G
  simp only [homologyIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom]
  rw [← Category.assoc, hG, Category.assoc, h, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientCohomology.Change
