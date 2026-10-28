import OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveCohomologyGenerators
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

/-! # Additive Iso Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.AdditiveIsoNaturality.AdditiveSheafCohomology

noncomputable section

section

/-! The integer source map used in the rational-to-additive comparison is natural under actual scheme isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

variable (R : Type 1) [Field R] [CharZero R] {X Y : Scheme.{0}} (e : X ≅ Y)

omit [CharZero R] in
theorem sourceMap_iso :
    (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor.map (AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology X)) ≫
      (AdditiveCohomologyFormula.AdditiveSheafCohomology.forgetField R (Scheme.ProEt.topology Y)).map
        ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant (ModuleCat.{1} R) e).hom.app (ModuleCat.of R R)) =
      (IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).hom.app (AddCommGrpCat.of (ULift.{1} ℤ)) ≫
        AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology Y) := by
  apply PeriodInvariants.ConstantSheafCoherence.transportedConstant_hom_ext Ab.{1} e
  apply NatTrans.ext
  funext U
  let V := (IntegralComparison.ProEtale.proEtaleCongr e).inverse.op.obj U
  let Z := AddCommGrpCat.of (ULift.{1} ℤ)
  let M := ModuleCat.of R R
  let F := AdditiveCohomologyGenerators.AdditiveSheafCohomology.forgetFieldCoefficients R
  have hx := congr_app (AdditiveCohomologyGenerators.AdditiveSheafCohomology.sourceMap_generator R (Scheme.ProEt.topology X)) V
  have hy := congr_app (AdditiveCohomologyGenerators.AdditiveSheafCohomology.sourceMap_generator R (Scheme.ProEt.topology Y)) U
  have hz := congr_app (PeriodInvariants.ConstantSheafCoherence.constantTransport_generators Ab.{1} e Z) U
  have hr := congr_app (PeriodInvariants.ConstantSheafCoherence.constantTransport_generators (ModuleCat.{1} R) e M) U
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) Z).app V ≫
      (AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology X)).hom.app V =
    AdditiveCohomologyGenerators.AdditiveSheafCohomology.coefficientUnit R ≫ F.map ((PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) M).app V) at hx
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) Z).app U ≫
      (AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology Y)).hom.app U =
    AdditiveCohomologyGenerators.AdditiveSheafCohomology.coefficientUnit R ≫ F.map ((PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) M).app U) at hy
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) Z).app V ≫
      (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).hom.app Z).hom.app U) =
    (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) Z).app U at hz
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) M).app V ≫
      (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant (ModuleCat.{1} R) e).hom.app M).hom.app U) =
    (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) M).app U at hr
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) Z).app V ≫
      (AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology X)).hom.app V ≫
        F.map (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant (ModuleCat.{1} R) e).hom.app M).hom.app U) =
    (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) Z).app V ≫
      (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).hom.app Z).hom.app U) ≫
        (AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology Y)).hom.app U
  erw [← Category.assoc, hx]
  erw [← Category.assoc ((PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) Z).app V)
    (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).hom.app Z).hom.app U), hz]
  change AdditiveCohomologyGenerators.AdditiveSheafCohomology.coefficientUnit R ≫ F.map ((PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) M).app V) ≫
      F.map (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant (ModuleCat.{1} R) e).hom.app M).hom.app U) = _
  erw [← F.map_comp]
  erw [hr]
  exact hy.symm

end

/-! The actual field-to-additive Ext comparison commutes with transport by scheme isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

variable (R : Type 1) [Field R] [CharZero R] {X Y : Scheme.{0}} (e : X ≅ Y)
  [HasExt.{1} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{1} ℤ))]
  [HasExt.{1} (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{1} ℤ))]

theorem equiv_iso (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{1} R)) (n : ℕ)
    (x : Ext (AdditiveSheaf.AdditiveSheafCohomology.fieldConstant R (Scheme.ProEt.topology X)) N n) :
    AdditiveSheaf.AdditiveSheafCohomology.equiv R (Scheme.ProEt.topology Y) ((IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{1} R) e).functor.obj N) n
      ((Ext.mk₀ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant (ModuleCat.{1} R) e).inv.app (ModuleCat.of R R))).comp
        (x.mapExactFunctor (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{1} R) e).functor) (zero_add n)) =
      (Ext.mk₀ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).inv.app
          (AddCommGrpCat.of (ULift.{1} ℤ)))).comp
        ((AdditiveSheaf.AdditiveSheafCohomology.equiv R (Scheme.ProEt.topology X) N n x).mapExactFunctor
          (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor) (zero_add n) := by
  let FX := AdditiveCohomologyFormula.AdditiveSheafCohomology.forgetField R (Scheme.ProEt.topology X)
  let FY := AdditiveCohomologyFormula.AdditiveSheafCohomology.forgetField R (Scheme.ProEt.topology Y)
  let ER := (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{1} R) e).functor
  let EA := (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor
  let r := (IntegralComparison.ProEtale.proEtaleSheafCongr_constant (ModuleCat.{1} R) e).app (ModuleCat.of R R)
  let z := (IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).app (AddCommGrpCat.of (ULift.{1} ℤ))
  let aX := AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology X)
  let aY := AdditiveCohomologyFormula.AdditiveSheafCohomology.sourceMap R (Scheme.ProEt.topology Y)
  have hs : aY ≫ FY.map r.inv = z.inv ≫ EA.map aX := by
    apply (cancel_mono (FY.map r.hom)).mp
    erw [Category.assoc, ← FY.map_comp, r.inv_hom_id, FY.map_id, Category.comp_id,
      Category.assoc, sourceMap_iso, ← Category.assoc, z.inv_hom_id, Category.id_comp]
  have he : (x.mapExactFunctor ER).mapExactFunctor FY =
      (x.mapExactFunctor FX).mapExactFunctor EA := by
    rw [← PeriodInvariants.ExtFunctoriality.mapExactFunctor_compFunctor ER FY,
      ← PeriodInvariants.ExtFunctoriality.mapExactFunctor_compFunctor FX EA]
    rfl
  rw [AdditiveCohomologyFormula.AdditiveSheafCohomology.equiv_apply, AdditiveCohomologyFormula.AdditiveSheafCohomology.equiv_apply]
  change (Ext.mk₀ aY).comp
      (((Ext.mk₀ r.inv).comp (x.mapExactFunctor ER) (zero_add n)).mapExactFunctor FY) (zero_add n) =
    (Ext.mk₀ z.inv).comp
      (((Ext.mk₀ aX).comp (x.mapExactFunctor FX) (zero_add n)).mapExactFunctor EA) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hs, he]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.AdditiveIsoNaturality.AdditiveSheafCohomology
