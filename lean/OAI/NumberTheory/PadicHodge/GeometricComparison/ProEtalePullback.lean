import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleConstant
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality

/-! # Pro Etale Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtalePullback.ProEtaleIsoCohomology

noncomputable section

/-! Original integral pullback along a scheme isomorphism is its exact-equivalence transport on sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTransport.ProEtaleIsoSheaves

private theorem transport_of_iso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasExt C] [HasExt D] [EnoughInjectives C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) {Z W : C} {T : D} (s : F.obj Z ≅ T) (t : G.obj Z ≅ T)
    (hs : s = e.app Z ≪≫ t) (n : ℕ) (x : Ext Z W n) :
    ((Ext.mk₀ s.inv).comp (x.mapExactFunctor F) (zero_add n)).comp
        (Ext.mk₀ (e.hom.app W)) (add_zero n) =
      (Ext.mk₀ t.inv).comp (x.mapExactFunctor G) (zero_add n) := by
  rw [Ext.comp_assoc_of_third_deg_zero, AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction.ext_mapExactFunctor_naturality F e.hom]
  rw [hs]
  simp only [Iso.trans_inv, Iso.app_inv, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, Category.assoc, e.inv_hom_id_app, Category.comp_id]

universe u
variable {X Y : Scheme.{u}} (e : X ≅ Y) (ℓ : ℕ) [Fact ℓ.Prime]

def transportPullback (n : ℕ) : Y.EllAdicCohomology ℓ n →+ X.EllAdicCohomology ℓ n :=
  ((Ext.mk₀ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).precomp
      (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) (zero_add n)).comp
    ((IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).functor.mapExtAddHom
      (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant Y) (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Y) n)

theorem integral_pullback (n : ℕ) (x : Y.EllAdicCohomology ℓ n) :
    AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.integralEllAdicPullback ℓ e.hom n x = transportPullback e ℓ n x := by
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  have hs : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso e.hom).app Z =
      (ProEtaleTransport.ProEtaleIsoSheaves.pullbackIso e).app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant Y) ≪≫
        (IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).app Z :=
    Iso.ext (ProEtaleConstant.ProEtaleIsoConstant.constant_pullback e Z)
  change (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Y).H n at x
  erw [AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullback_apply, ProEtaleTransport.ProEtaleIsoSheaves.coefficient_pullback]
  exact transport_of_iso (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback e.hom)
    (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).functor (ProEtaleTransport.ProEtaleIsoSheaves.pullbackIso e)
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso e.hom).app Z)
    ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{u + 1} e.symm).app Z) hs n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtalePullback.ProEtaleIsoCohomology
