import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Coefficient Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientChange

noncomputable section

/-! Product-preserving additive coefficient change on the original
augmented ordered Čech complex, including every actual restriction map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  (P : Cᵒᵖ ⥤ A)

def objectIso (n : ℕ) : G.obj (AugmentedOrdered.Cech.object U P n) ≅ AugmentedOrdered.Cech.object U (P ⋙ G) n :=
  PreservesProduct.iso G (fun a : AugmentedOrdered.Cech.Index ι n => P.obj (op ((AugmentedOrdered.Cech.formal U n).obj a)))

omit [Preadditive A] [Preadditive B] [G.Additive] in
theorem coface (n : ℕ) (k : Fin (n+1)) :
    G.map (AugmentedOrdered.Cech.coface U P n k) ≫ (objectIso U G P (n+1)).hom =
      (objectIso U G P n).hom ≫ AugmentedOrdered.Cech.coface U (P ⋙ G) n k :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.piComparison_natural G
    (fun a : AugmentedOrdered.Cech.Index ι n => P.obj (op ((AugmentedOrdered.Cech.formal U n).obj a)))
    (fun a : AugmentedOrdered.Cech.Index ι (n+1) => P.obj (op ((AugmentedOrdered.Cech.formal U (n+1)).obj a)))
    (AugmentedOrdered.Cech.face U n k).f (fun a => P.map ((AugmentedOrdered.Cech.face U n k).φ a).op)

theorem differential (n : ℕ) :
    G.map (AugmentedOrdered.Cech.differential U P n) ≫ (objectIso U G P (n+1)).hom =
      (objectIso U G P n).hom ≫ AugmentedOrdered.Cech.differential U (P ⋙ G) n := by
  simp only [AugmentedOrdered.Cech.differential, Functor.map_sum, Functor.map_zsmul,
    sum_comp, comp_sum, zsmul_comp, comp_zsmul, coface]

def complexIso : (G.mapHomologicalComplex (.up ℕ)).obj (AugmentedOrdered.Cech.complex U P) ≅ AugmentedOrdered.Cech.complex U (P ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents (objectIso U G P) (by
    intro n m hnm
    obtain rfl : m = n+1 := hnm.symm
    change (objectIso U G P n).hom ≫ (AugmentedOrdered.Cech.complex U (P ⋙ G)).d n (n+1) =
      G.map ((AugmentedOrdered.Cech.complex U P).d n (n+1)) ≫ (objectIso U G P (n+1)).hom
    rw [show (AugmentedOrdered.Cech.complex U P).d n (n+1) = AugmentedOrdered.Cech.differential U P n from
      CochainComplex.of_d _ _ n,
      show (AugmentedOrdered.Cech.complex U (P ⋙ G)).d n (n+1) = AugmentedOrdered.Cech.differential U (P ⋙ G) n from
      CochainComplex.of_d _ _ n]
    exact (differential U G P n).symm)

theorem naturality {Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (G.mapHomologicalComplex (.up ℕ)).map (AugmentedOrdered.CechFunctor.complexMap U f) ≫ (complexIso U G Q).hom =
      (complexIso U G P).hom ≫ AugmentedOrdered.CechFunctor.complexMap U (Functor.whiskerRight f G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map G
    (fun a : AugmentedOrdered.Cech.Index ι n => f.app (op ((AugmentedOrdered.Cech.formal U n).obj a)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientChange
