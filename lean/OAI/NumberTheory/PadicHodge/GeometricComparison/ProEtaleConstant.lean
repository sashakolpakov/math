import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTransport
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

/-! # Pro Etale Constant -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleConstant.ProEtaleIsoConstant

noncomputable section

/-! The actual integral constant-coefficient maps agree under transport by a scheme isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleStructure.ProEtaleIsoSite OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTransport.ProEtaleIsoSheaves

universe u
variable {X Y : Scheme.{u}} (e : X ≅ Y) (P : Ab.{u + 1})

theorem pushforward_generators :
    PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) P ≫
      (AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantToPushforward e.hom P ≫
        (ProEtaleTransport.ProEtaleIsoSheaves.pushforwardIso e).hom.app ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj P)).hom =
      whiskerLeft (IntegralComparison.ProEtale.proEtaleCongr e.symm).functor.op
        (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) P) := by
  apply NatTrans.ext
  funext U
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) P).app U ≫
    (AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantToPushforward e.hom P).hom.app U ≫
      ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj P).obj.map
        ((ProEtaleStructure.ProEtaleIsoSite.baseChangeIso e).inv.app U.unop).op =
      (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) P).app
        ((IntegralComparison.ProEtale.proEtaleCongr e.symm).functor.op.obj U)
  erw [AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantToPushforward_unit_app_assoc]
  exact PeriodInvariants.ConstantSheafCoherence.constantGenerator_naturality (Scheme.ProEt.topology X) P
    ((ProEtaleStructure.ProEtaleIsoSite.baseChangeIso e).inv.app U.unop).op

theorem transport_adjunction_generators :
    PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) P ≫
      (((IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).toAdjunction.homEquiv _ _)
        ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).hom.app P)).hom =
      whiskerLeft (IntegralComparison.ProEtale.proEtaleCongr e.symm).functor.op
        (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology X) P) := by
  rw [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext U
  let V := (IntegralComparison.ProEtale.proEtaleCongr e.symm).functor.op.obj U
  change (PeriodInvariants.ConstantSheafCoherence.constantGenerator (Scheme.ProEt.topology Y) P).app U ≫
    ((constantSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).obj P).obj.map
      ((IntegralComparison.ProEtale.proEtaleCongr e.symm).op.unitIso.hom.app U) ≫
        ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).hom.app P).hom.app V = _
  erw [← Category.assoc, PeriodInvariants.ConstantSheafCoherence.constantGenerator_naturality]
  exact congr_app (PeriodInvariants.ConstantSheafCoherence.constantTransport_generators Ab.{u + 1} e.symm P) V

theorem constant_pullback :
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso e.hom).hom.app P =
      (ProEtaleTransport.ProEtaleIsoSheaves.pullbackIso e).hom.app ((constantSheaf (Scheme.ProEt.topology Y) Ab.{u + 1}).obj P) ≫
        (IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).hom.app P := by
  let a := (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange e.hom).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let b := a.ofNatIsoRight (ProEtaleTransport.ProEtaleIsoSheaves.pushforwardIso e)
  let c := (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).toAdjunction
  have h : AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantToPushforward e.hom P ≫
      (ProEtaleTransport.ProEtaleIsoSheaves.pushforwardIso e).hom.app ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj P) =
      c.homEquiv _ _ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).hom.app P) := by
    apply PeriodInvariants.ConstantSheafCoherence.constant_hom_ext
    exact (pushforward_generators e P).trans (transport_adjunction_generators e P).symm
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso e.hom).hom.app P) =
    b.homEquiv _ _ (((b.leftAdjointUniq c).hom.app _) ≫
      (IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).hom.app P)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  erw [Adjunction.homEquiv_ofNatIsoRight_apply, AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantPullbackIso_adjoint]
  exact h.trans (c.homEquiv_unit _ _ _)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleConstant.ProEtaleIsoConstant
