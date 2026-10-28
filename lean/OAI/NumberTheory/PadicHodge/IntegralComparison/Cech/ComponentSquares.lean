import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates

/-! # Component Squares -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComponentSquares

noncomputable section

/-! Projection tests for literal component maps into the ordered Čech
objects, before any coefficient complexes are substituted. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  {A B : D} (δ : A ⟶ B)

omit [Preadditive D] in
theorem horizontal_projection {P Q : Cᵒᵖ ⥤ D} (d : P ⟶ Q) (q : ℕ)
    (f : ∀ a : AugmentedOrdered.Cech.Index ι q, A ⟶ P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a))) (a : AugmentedOrdered.Cech.Index ι q) :
    (Pi.lift f ≫ AugmentedOrdered.CechFunctor.objectMap U d q) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι q => Q.obj (op ((AugmentedOrdered.Cech.formal U q).obj b))) a =
      f a ≫ d.app (op ((AugmentedOrdered.Cech.formal U q).obj a)) :=
  (Category.assoc _ _ _).trans ((congrArg (Pi.lift f ≫ ·) (AugmentedOrdered.CechCoordinates.objectMap_comp_pi U P d q a)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ d.app _) (Pi.lift_comp_π f a))))

omit [Preadditive D] in
theorem horizontal {P Q : Cᵒᵖ ⥤ D} (d : P ⟶ Q) (q : ℕ)
    (f : ∀ a : AugmentedOrdered.Cech.Index ι q, A ⟶ P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (g : ∀ a : AugmentedOrdered.Cech.Index ι q, B ⟶ Q.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (h : ∀ a, f a ≫ d.app (op ((AugmentedOrdered.Cech.formal U q).obj a)) = δ ≫ g a) :
    Pi.lift f ≫ AugmentedOrdered.CechFunctor.objectMap U d q = δ ≫ Pi.lift g := by
  apply Pi.hom_ext
  intro a
  exact (horizontal_projection U d q f a).trans ((h a).trans
    ((Category.assoc _ _ _).trans (congrArg (δ ≫ ·) (Pi.lift_comp_π g a))).symm)

theorem vertical_projection (P : Cᵒᵖ ⥤ D) (q : ℕ)
    (f : ∀ a : AugmentedOrdered.Cech.Index ι q, A ⟶ P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a))) (a : AugmentedOrdered.Cech.Index ι (q + 1)) :
    (Pi.lift f ≫ AugmentedOrdered.Cech.differential U P q) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index ι (q + 1) => P.obj (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj b))) a =
      ∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val • (f (a.delete k) ≫ P.map ((AugmentedOrdered.Cech.face U q k).φ a).op) := by
  refine (Category.assoc _ _ _).trans
    ((congrArg (Pi.lift f ≫ ·) (AugmentedOrdered.CechCoordinates.differential_comp_pi U P q a)).trans ?_)
  rw [comp_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [comp_zsmul]
  exact congrArg (fun z => (-1 : ℤ) ^ k.val • z)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.map ((AugmentedOrdered.Cech.face U q k).φ a).op)
      (Pi.lift_comp_π f (a.delete k))))

theorem vertical (P : Cᵒᵖ ⥤ D) (q : ℕ)
    (f : ∀ a : AugmentedOrdered.Cech.Index ι q, A ⟶ P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (g : ∀ a : AugmentedOrdered.Cech.Index ι (q + 1), B ⟶ P.obj (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj a)))
    (h : ∀ a, (∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val •
      (f (a.delete k) ≫ P.map ((AugmentedOrdered.Cech.face U q k).φ a).op)) = δ ≫ g a) :
    Pi.lift f ≫ AugmentedOrdered.Cech.differential U P q = δ ≫ Pi.lift g := by
  apply Pi.hom_ext
  intro a
  exact (vertical_projection U P q f a).trans ((h a).trans
    ((Category.assoc _ _ _).trans (congrArg (δ ≫ ·) (Pi.lift_comp_π g a))).symm)

theorem mixed {P Q : Cᵒᵖ ⥤ D} (d : P ⟶ Q) (q : ℕ) (sign : ℤ)
    (f₀ : ∀ a : AugmentedOrdered.Cech.Index ι (q + 1), A ⟶ P.obj (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj a)))
    (f₁ : ∀ a : AugmentedOrdered.Cech.Index ι q, A ⟶ Q.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (g : ∀ a : AugmentedOrdered.Cech.Index ι (q + 1), B ⟶ Q.obj (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj a)))
    (h : ∀ a, f₀ a ≫ d.app (op ((AugmentedOrdered.Cech.formal U (q + 1)).obj a)) +
      sign • (∑ k : Fin (q + 1), (-1 : ℤ) ^ k.val •
        (f₁ (a.delete k) ≫ Q.map ((AugmentedOrdered.Cech.face U q k).φ a).op)) = δ ≫ g a) :
    Pi.lift f₀ ≫ AugmentedOrdered.CechFunctor.objectMap U d (q + 1) + sign • (Pi.lift f₁ ≫ AugmentedOrdered.Cech.differential U Q q) =
      δ ≫ Pi.lift g := by
  apply Pi.hom_ext
  intro a
  refine (add_comp _ _ _ _ _ _).trans ?_
  refine (congrArg₂ (· + ·) (horizontal_projection U d (q + 1) f₀ a)
    ((zsmul_comp _ _ _).trans
      (congrArg (fun z => sign • z) (vertical_projection U Q q f₁ a)))).trans ?_
  exact (h a).trans
    ((Category.assoc _ _ _).trans (congrArg (δ ≫ ·) (Pi.lift_comp_π g a))).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComponentSquares
