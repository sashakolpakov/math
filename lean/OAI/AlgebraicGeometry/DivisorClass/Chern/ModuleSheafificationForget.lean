import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.SheafForget
import OAI.AlgebraicTopology.DeRham.Comparison.RationalSheafForget
import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Module Sheafification Forget -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleSheafificationForget

noncomputable section

/-! Canonical sheafification comparison when module scalars are forgotten. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [Ring R] (X : TopCat.{0})

instance moduleForget_preservesSheafification :
    (Opens.grothendieckTopology X).PreservesSheafification (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) where
  le {P Q} f hf := by
    obtain ⟨hi, hs⟩ := ((Opens.grothendieckTopology X).W_iff_isLocallyBijective f).mp hf
    apply ((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).mpr
    constructor
    · exact ⟨fun x y h => hi.equalizerSieve_mem x y h⟩
    · exact ⟨fun s => hs.imageSieve_mem s⟩

instance moduleForgetSheaf_additive :
    (sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})).Additive where
  map_add := rfl

def moduleForgetSheafificationIso (P : X.Presheaf (ModuleCat.{0} R)) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
      (P ⋙ forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) ≅
    (sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj P) :=
  (sheafComposeNatIso (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})
    (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} R))
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0})).app P

theorem moduleForgetSheafificationIso_unit (P : X.Presheaf (ModuleCat.{0} R)) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (P ⋙ forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) ≫ (moduleForgetSheafificationIso R X P).hom.hom =
      Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)
        (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) :=
  sheafComposeNatTrans_fac _ _ _ _ _

def moduleForgetPresheafComplex (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) :
    CochainComplex (X.Presheaf AddCommGrpCat.{0}) ℕ :=
  (((Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat.{0} R) AddCommGrpCat.{0}).obj
    (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})).mapHomologicalComplex (.up ℕ)).obj K

def moduleForgetSheafComplex (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})).mapHomologicalComplex (.up ℕ)).obj K

def abelianSheafifiedCochainComplex (K : CochainComplex (X.Presheaf AddCommGrpCat.{0}) ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).obj K

def moduleForgetSheafificationComplexIso (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) :
    abelianSheafifiedCochainComplex X (moduleForgetPresheafComplex R X K) ≅
      moduleForgetSheafComplex R X (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => moduleForgetSheafificationIso R X (K.X n)) (by
    intro i j _
    exact ((sheafComposeNatIso (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})
      (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} R))
      (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0})).hom.naturality (K.d i j)).symm)

theorem moduleForgetSheafificationComplexIso_f_unit
    (K : CochainComplex (X.Presheaf (ModuleCat.{0} R)) ℕ) (n : ℕ) :
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        ((moduleForgetPresheafComplex R X K).X n) ≫
        ((moduleForgetSheafificationComplexIso R X K).hom.f n).hom =
      Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (K.X n))
        (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}) :=
  moduleForgetSheafificationIso_unit R X (K.X n)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ModuleSheafificationForget
