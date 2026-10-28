import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleStructure
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence

/-! # Pro Etale Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTransport.ProEtaleIsoSheaves

noncomputable section

/-! Compare the actual integral inverse-image functor with sheaf transport by a scheme isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleStructure.ProEtaleIsoSite

universe u
variable {X Y : Scheme.{u}} (e : X ≅ Y)

def pushforwardIso :
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange e.hom).sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) ≅
      (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).inverse :=
  Functor.sheafPushforwardContinuousIso (ProEtaleStructure.ProEtaleIsoSite.baseChangeIso e) Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

def pullbackIso : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback e.hom ≅ (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).functor :=
  (((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange e.hom).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).ofNatIsoRight (pushforwardIso e)).leftAdjointUniq
      (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).toAdjunction

def coefficientTransport (ℓ : ℕ) [Fact ℓ.Prime] :
    (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).functor.obj (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Y) ≅
      AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X := eqToIso rfl

theorem coefficient_toPushforward (ℓ : ℕ) [Fact ℓ.Prime] :
    AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientToPushforward ℓ e.hom ≫
      (pushforwardIso e).hom.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) = 𝟙 _ := by
  ext U s
  change ULift.{u + 1} C(U.unop.left, ℤ_[ℓ]) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change s.down ((pullback.fst U.unop.hom e.hom)
    (((ProEtaleStructure.ProEtaleIsoSite.baseChangeIso e).inv.app U.unop).left x)) = s.down x
  exact congrArg (fun f : U.unop.left ⟶ U.unop.left => s.down (f x))
    (ProEtaleStructure.ProEtaleIsoSite.projectionIso e U.unop.hom).inv_hom_id

theorem coefficient_pullback (ℓ : ℕ) [Fact ℓ.Prime] :
    AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientPullback ℓ e.hom =
      (pullbackIso e).hom.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Y) := by
  let a := (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange e.hom).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let b := a.ofNatIsoRight (pushforwardIso e)
  let c := (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{u + 1} e.symm).toAdjunction
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientPullback ℓ e.hom) =
    b.homEquiv _ _ ((b.leftAdjointUniq c).hom.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Y))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  erw [Adjunction.homEquiv_ofNatIsoRight_apply]
  change a.homEquiv _ _ ((a.homEquiv _ _).symm (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientToPushforward ℓ e.hom)) ≫ _ = _
  rw [Equiv.apply_symm_apply, coefficient_toPushforward]
  symm
  ext U s
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTransport.ProEtaleIsoSheaves
