import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex

/-! # Augmentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.Augmentation

noncomputable section

/-! Restricting a global section to ordered Čech intersections gives an actual zero cycle in degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def orderedCechSectionMap (q : ℕ) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤) ⟶ Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q :=
  CategoryTheory.Limits.Pi.lift fun a : Ordered.SectionCechIndices.OrderedCechIndex ι q ↦
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map
      (homOfLE (show (∏ᶜ fun k : Fin (q + 1) ↦ U (a.val k)) ≤ ⊤ from le_top)).op

theorem orderedCechSectionMap_comp_π (q : ℕ) (a : Ordered.SectionCechIndices.OrderedCechIndex ι q) :
    orderedCechSectionMap c M U q ≫ CategoryTheory.Limits.Pi.π
      (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι q ↦ Ordered.CoefficientCechTerms.coefficientCechFactor c M U q b.val) a =
    (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map
      (homOfLE (show (∏ᶜ fun k : Fin (q + 1) ↦ U (a.val k)) ≤ ⊤ from le_top)).op :=
  CategoryTheory.Limits.Pi.lift_comp_π _ a

theorem orderedCechSectionMap_comp_coface (q : ℕ) (k : Fin (q + 2)) :
    orderedCechSectionMap c M U q ≫ Ordered.CoefficientCechTerms.orderedCoefficientCechCoface c M U q k =
      orderedCechSectionMap c M U (q + 1) := by
  apply CategoryTheory.Limits.Pi.hom_ext
    (f := fun a : Ordered.SectionCechIndices.OrderedCechIndex ι (q + 1) ↦ Ordered.CoefficientCechTerms.coefficientCechFactor c M U (q + 1) a.val)
  intro a
  let F := Coefficient.ModulePresheaf.coefficientModulePresheaf c M
  let A : ModuleCat.{u} R := F.obj (op ⊤)
  let B : ModuleCat.{u} R := Ordered.CoefficientCechTerms.coefficientCechFactor c M U q (a.delete k).val
  let D : ModuleCat.{u} R := Ordered.CoefficientCechTerms.coefficientCechFactor c M U (q + 1) a.val
  let p : Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q ⟶ B := CategoryTheory.Limits.Pi.π
    (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι q ↦ Ordered.CoefficientCechTerms.coefficientCechFactor c M U q b.val) (a.delete k)
  let t : Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U (q + 1) ⟶ D := CategoryTheory.Limits.Pi.π
    (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι (q + 1) ↦ Ordered.CoefficientCechTerms.coefficientCechFactor c M U (q + 1) b.val) a
  let r : B ⟶ D := F.map (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ a.val).op
  have hc : Ordered.CoefficientCechTerms.orderedCoefficientCechCoface c M U q k ≫ t = p ≫ r :=
    Ordered.CoefficientCechTerms.orderedCoefficientCechCoface_comp_π c M U q k a
  have hcomp : (orderedCechSectionMap c M U q ≫ p) ≫ r =
      F.map (homOfLE (show (∏ᶜ fun j : Fin (q + 2) ↦ U (a.val j)) ≤ ⊤ from le_top)).op := by
    calc
      _ = F.map (homOfLE (show (∏ᶜ fun j : Fin (q + 1) ↦ U ((a.delete k).val j)) ≤ ⊤
          from le_top)).op ≫ r :=
        congrArg (fun f : A ⟶ B ↦ f ≫ r) (orderedCechSectionMap_comp_π c M U q (a.delete k))
      _ = _ := (F.map_comp _ _).symm.trans (congrArg F.map (Subsingleton.elim _ _))
  exact (Category.assoc _ _ t).trans
    ((congrArg (fun f : Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q ⟶ D ↦
      orderedCechSectionMap c M U q ≫ f) hc).trans
        ((Category.assoc _ p r).symm.trans
          (hcomp.trans (orderedCechSectionMap_comp_π c M U (q + 1) a).symm)))

theorem orderedCechSectionMap_comp_differential :
    orderedCechSectionMap c M U 0 ≫ Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential c M U 0 = 0 := by
  rw [Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential, Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul, orderedCechSectionMap_comp_coface]
  change (∑ k : Fin 2, (-1 : ℤ) ^ k.val • orderedCechSectionMap c M U 1) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    Fin.val_one, pow_one, neg_one_zsmul, add_neg_cancel]

def orderedCechSectionToCycles : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op ⊤) →ₗ[R]
    ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).d 0 1).hom.ker :=
  (orderedCechSectionMap c M U 0).hom.codRestrict _ (by
    intro x
    change ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).d 0 1).hom
      ((orderedCechSectionMap c M U 0).hom x) = 0
    rw [Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d]
    exact ConcreteCategory.congr_hom (orderedCechSectionMap_comp_differential c M U) x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.Augmentation
