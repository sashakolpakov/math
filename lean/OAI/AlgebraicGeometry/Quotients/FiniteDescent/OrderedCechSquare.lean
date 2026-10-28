import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech

/-! # Ordered Cech Square -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare

noncomputable section

/-! The restriction of global sections to ordered Cech zero-cycles. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.OrderedCechAugmentation

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def map : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) ⟶ (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).X 0 :=
  Pi.lift (fun i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 =>
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op)

theorem map_π (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    OrderedCechAugmentation.map π M U ≫ Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 j.1) i =
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op :=
  Pi.lift_comp_π _ i

theorem map_coface_π (k : Fin 2) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1) :
    OrderedCechAugmentation.map π M U ≫ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 k ≫
      Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 1 j.1) i =
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op := by
  rw [SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface_comp_π, ← Category.assoc, map_π,
    ← (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map_comp]
  exact (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).congr_map (Subsingleton.elim _ _)

private theorem alternating_two {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (a : A ⟶ B) (d : Fin 2 → (B ⟶ D)) (h : a ≫ d 0 = a ≫ d 1) :
    a ≫ (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • d k) = 0 := by
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, Preadditive.comp_add, Preadditive.comp_neg]
  rw [h, add_neg_cancel]

theorem square : OrderedCechAugmentation.map π M U ≫ (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1 = 0 := by
  have h : OrderedCechAugmentation.map π M U ≫ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 0 =
      OrderedCechAugmentation.map π M U ≫ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0 1 := by
    apply Pi.hom_ext (f := fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 1 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 1 j.1)
    intro i
    simp only [Category.assoc]
    exact (map_coface_π π M U 0 i).trans (map_coface_π π M U 1 i).symm
  exact alternating_two (OrderedCechAugmentation.map π M U) (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechCoface π M U 0) h

def toCycles : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) →ₗ[Γ(S, ⊤)]
    ((SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).d 0 1).hom.ker :=
  (OrderedCechAugmentation.map π M U).hom.codRestrict _ (fun s => ConcreteCategory.congr_hom (square π M U) s)

theorem toCycles_π (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤)) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) :
    Pi.π (fun j : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0 => SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U 0 j.1) i (toCycles π M U s).val =
      M.presheaf.map (homOfLE (show (∏ᶜ fun k => U (i.1 k)) ≤ ⊤ from le_top)).op s :=
  ConcreteCategory.congr_hom (map_π π M U i) s

end Construction.OrderedCechAugmentation

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare
