import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

/-! # Constant Transport -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantTransport

noncomputable section

/-!
# Identity and composition of canonical constant-sheaf transport

The identifications are the actual adjunction-defined maps. Their coherence
follows from preservation of the sheafification generators.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.PeriodInvariants.ProEtaleCoherence OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

variable (A : Type*) [Category A]
variable {X Y Z : Scheme.{u}}
variable [HasWeakSheafify (Scheme.ProEt.topology X) A]
  [HasWeakSheafify (Scheme.ProEt.topology Y) A]
  [HasWeakSheafify (Scheme.ProEt.topology Z) A]

theorem constantTransport_refl (X : Scheme.{u})
    [HasWeakSheafify (Scheme.ProEt.topology X) A] (a : A) :
    (ProEtaleCoherence.proEtaleSheafCongr_refl A X).hom.app ((constantSheaf (Scheme.ProEt.topology X) A).obj a) =
      (IntegralComparison.ProEtale.proEtaleSheafCongr_constant A (Iso.refl X)).hom.app a := by
  apply ConstantSheafCoherence.transportedConstant_hom_ext A (Iso.refl X)
  rw [ConstantSheafCoherence.constantTransport_generators]
  apply NatTrans.ext
  funext U
  have hm : ((ProEtaleCoherence.proEtaleSheafCongr_refl A X).hom.app
      ((constantSheaf (Scheme.ProEt.topology X) A).obj a)).hom.app U =
      ((constantSheaf (Scheme.ProEt.topology X) A).obj a).obj.map
        (((ProEtaleCoherence.proEtaleCongr_refl X).inv.app U.unop).op) := by
    exact Category.comp_id _
  exact (congrArg (fun z => (ConstantSheafCoherence.transportedConstantGenerator A (Iso.refl X) a).app U ≫ z) hm).trans
    (ConstantSheafCoherence.constantGenerator_naturality (Scheme.ProEt.topology X) a
      (((ProEtaleCoherence.proEtaleCongr_refl X).inv.app U.unop).op))

omit [HasWeakSheafify (Scheme.ProEt.topology Y) A]
  [HasWeakSheafify (Scheme.ProEt.topology Z) A] in
theorem transportedConstantGenerator_comp (e : X ≅ Y) (f : Y ≅ Z) (a : A) :
    ConstantSheafCoherence.transportedConstantGenerator A (e ≪≫ f) a ≫
        ((ProEtaleCoherence.proEtaleSheafCongr_comp A e f).inv.app
          ((constantSheaf (Scheme.ProEt.topology X) A).obj a)).hom =
      whiskerLeft (IntegralComparison.ProEtale.proEtaleCongr f).inverse.op (ConstantSheafCoherence.transportedConstantGenerator A e a) := by
  apply NatTrans.ext
  funext U
  have hm : ((ProEtaleCoherence.proEtaleSheafCongr_comp A e f).inv.app
      ((constantSheaf (Scheme.ProEt.topology X) A).obj a)).hom.app U =
      ((constantSheaf (Scheme.ProEt.topology X) A).obj a).obj.map
        (((ProEtaleCoherence.proEtaleCongr_comp f.symm e.symm).inv.app U.unop).op) := by
    exact Category.comp_id _
  exact (congrArg (fun z => (ConstantSheafCoherence.transportedConstantGenerator A (e ≪≫ f) a).app U ≫ z) hm).trans
    (ConstantSheafCoherence.constantGenerator_naturality (Scheme.ProEt.topology X) a
      (((ProEtaleCoherence.proEtaleCongr_comp f.symm e.symm).inv.app U.unop).op))

theorem constantTransport_comp (e : X ≅ Y) (f : Y ≅ Z) (a : A) :
    (IntegralComparison.ProEtale.proEtaleSheafCongr A f).functor.map
        ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant A e).hom.app a) ≫
        (IntegralComparison.ProEtale.proEtaleSheafCongr_constant A f).hom.app a =
      (ProEtaleCoherence.proEtaleSheafCongr_comp A e f).hom.app
        ((constantSheaf (Scheme.ProEt.topology X) A).obj a) ≫
        (IntegralComparison.ProEtale.proEtaleSheafCongr_constant A (e ≪≫ f)).hom.app a := by
  apply (cancel_epi ((ProEtaleCoherence.proEtaleSheafCongr_comp A e f).inv.app
    ((constantSheaf (Scheme.ProEt.topology X) A).obj a))).mp
  rw [Iso.inv_hom_id_app_assoc]
  apply ConstantSheafCoherence.transportedConstant_hom_ext A (e ≪≫ f)
  rw [ConstantSheafCoherence.constantTransport_generators]
  change ConstantSheafCoherence.transportedConstantGenerator A (e ≪≫ f) a ≫
    ((ProEtaleCoherence.proEtaleSheafCongr_comp A e f).inv.app
      ((constantSheaf (Scheme.ProEt.topology X) A).obj a)).hom ≫
      (whiskerLeft (IntegralComparison.ProEtale.proEtaleCongr f).inverse.op
        ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant A e).hom.app a).hom ≫
          ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant A f).hom.app a).hom) = _
  rw [← Category.assoc (ConstantSheafCoherence.transportedConstantGenerator A (e ≪≫ f) a),
    transportedConstantGenerator_comp]
  apply NatTrans.ext
  funext U
  have he := congrArg (fun η => η.app ((IntegralComparison.ProEtale.proEtaleCongr f).inverse.op.obj U))
    (ConstantSheafCoherence.constantTransport_generators A e a)
  have hf := congrArg (fun η => η.app U) (ConstantSheafCoherence.constantTransport_generators A f a)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant A f).hom.app a).hom.app U)) he).trans hf)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantTransport
