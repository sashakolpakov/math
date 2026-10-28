/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCech.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ProductForget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.CoefficientCechComplex

/-! # Formal Coproduct Forget -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FormalCoproductForget

noncomputable section

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u

noncomputable def evalOpForgetIsoApp
    {C : Type u} [Category.{u} C] (R : Type u) [Ring R]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) (V : (FormalCoproduct C)ᵒᵖ) :
    (((FormalCoproduct.evalOp C (ModuleCat.{u} R)).obj P ⋙
        Module.ProductForget.moduleForget R).obj V) ≅
      (((FormalCoproduct.evalOp C AddCommGrpCat.{u}).obj
        (P ⋙ Module.ProductForget.moduleForget R)).obj V) := by
  change (Module.ProductForget.moduleForget R).obj
      (∏ᶜ fun i : V.unop.I => P.obj (op (V.unop.obj i))) ≅
    ∏ᶜ fun i : V.unop.I =>
      (Module.ProductForget.moduleForget R).obj (P.obj (op (V.unop.obj i)))
  exact Module.ProductForget.modulePiForgetIso R fun i => P.obj (op (V.unop.obj i))

/-- Evaluation of a module-valued presheaf on a formal coproduct commutes with
forgetting to additive groups. -/
noncomputable def evalOpForgetIso
    {C : Type u} [Category.{u} C] (R : Type u) [Ring R]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    (FormalCoproduct.evalOp C (ModuleCat.{u} R)).obj P ⋙
        Module.ProductForget.moduleForget R ≅
      (FormalCoproduct.evalOp C AddCommGrpCat.{u}).obj
        (P ⋙ Module.ProductForget.moduleForget R) :=
  NatIso.ofComponents (evalOpForgetIsoApp R P) (by
        intro V W f
        exact Module.ProductForget.modulePiForgetIso_naturality R
          (fun i : V.unop.I => P.obj (op (V.unop.obj i)))
          (fun i : W.unop.I => P.obj (op (W.unop.obj i)))
          f.unop.f (fun i => P.map (f.unop.φ i).op))

/-- The evaluation comparison from a forgotten module product to the additive
product commutes with every projection. -/
@[reassoc]
theorem evalOpForgetIso_hom_π
    {C : Type u} [Category.{u} C] (R : Type u) [Ring R]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R)
    (V : (FormalCoproduct C)ᵒᵖ) (i : V.unop.I) :
    (evalOpForgetIso R P).hom.app V ≫
        Pi.π (fun j => (Module.ProductForget.moduleForget R).obj
          (P.obj (op (V.unop.obj j)))) i =
      (Module.ProductForget.moduleForget R).map
        (Pi.π (fun j => P.obj (op (V.unop.obj j))) i) :=
  Module.ProductForget.modulePiForgetIso_hom_π R
    (fun j => P.obj (op (V.unop.obj j))) i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FormalCoproductForget
