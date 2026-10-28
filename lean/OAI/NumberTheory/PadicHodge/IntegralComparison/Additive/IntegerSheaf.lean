import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafCoefficients
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Topology.Sheaves.Flasque

/-! # Integer Sheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.IntegerSheaf

noncomputable section

/-! Canonical integer coefficients retain the literal underlying
additive groups, section maps, and flasque property. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u

def coefficients : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

instance coefficients_additive : coefficients.{u}.Additive where
  map_add := rfl

def underlyingIso : coefficients.{u} ⋙ forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} ≅
    𝟭 AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

instance coefficients_equivalence : coefficients.{u}.IsEquivalence := by
  let : (coefficients.{u} ⋙ forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).IsEquivalence :=
    CategoryTheory.Functor.isEquivalence_of_iso underlyingIso.symm
  exact CategoryTheory.Functor.isEquivalence_of_comp_right
    coefficients.{u} (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})

variable (X : TopCat.{u})

def sheaves : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} ℤ) :=
  sheafCompose (Opens.grothendieckTopology X) coefficients.{u}

instance sheaves_additive : (sheaves X).Additive where
  map_add := by
    intro P Q f g
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rfl

instance sheaves_equivalence : (sheaves X).IsEquivalence :=
  PeriodInvariants.SheafCoefficients.compose_equivalence (Opens.grothendieckTopology X)
    coefficients.{u}.asEquivalence

def underlyingSheavesIso : sheaves X ⋙
    sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) ≅
      𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

theorem flasque (P : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque P] : TopCat.Sheaf.IsFlasque ((sheaves X).obj P) where
  epi j := by
    change Epi (coefficients.{u}.map (P.obj.map j))
    infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.IntegerSheaf
