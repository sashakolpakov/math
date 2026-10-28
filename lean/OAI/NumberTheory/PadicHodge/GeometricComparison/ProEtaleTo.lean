import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleFst
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence

/-! # Pro Etale To -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTo.ProEtaleFrobeniusSheaves

noncomputable section

/-! The Frobenius site isomorphism identifies the original inverse-image functor and its actual integral and constant coefficient maps with the identity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleFst.ProEtaleFrobeniusSite

universe u
variable (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0)

def pushforwardIso :
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (ProEtaleFst.ProEtaleFrobeniusSite.baseChangeIso p hp X hX).symm _ _

def pullbackIso : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) ≅ 𝟭 _ :=
  ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)).leftAdjointIdIso
    (pushforwardIso p hp X hX)

theorem coefficient_toPushforward (ℓ : ℕ) [Fact ℓ.Prime] :
    AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientToPushforward ℓ (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) ≫
      (pushforwardIso p hp X hX).hom.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) = 𝟙 _ := by
  ext U s
  change ULift.{u + 1} (ContinuousMap U.unop.left (ℤ_[ℓ])) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change s.down ((pullback.fst U.unop.hom (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX))
    (((ProEtaleFst.ProEtaleFrobeniusSite.baseChangeIso p hp X hX).hom.app U.unop).left x)) = s.down x
  exact congrArg (fun f : U.unop.left ⟶ U.unop.left => s.down (f x))
    (ProEtaleFst.ProEtaleFrobeniusSite.component_fst p hp X hX U.unop)

theorem coefficient_pullback (ℓ : ℕ) [Fact ℓ.Prime] :
    AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientPullback ℓ (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) =
      (pullbackIso p hp X hX).hom.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) := by
  have h : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientToPushforward ℓ (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX) =
      (pushforwardIso p hp X hX).inv.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) := by
    rw [← cancel_mono ((pushforwardIso p hp X hX).hom.app (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X)),
      coefficient_toPushforward, Iso.inv_hom_id_app]
    rfl
  unfold AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtCoefficientPullback
  rw [h]
  exact AlgebraicGeometry.FormalGeometry.Completion.AdjunctionCoherence.Construction.adjunction_id_adjoint
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (pushforwardIso p hp X hX) (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X)

theorem constant_pullback (P : Ab.{u + 1}) :
    (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).hom.app P =
      (pullbackIso p hp X hX).hom.app
        ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj P) := by
  let a := (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology X)
  let c := constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
    (terminalIsTerminal (C := X.ProEt))
  apply ((c.comp a).homEquiv _ _).injective
  change (c.comp a).homEquiv _ _
    (((c.comp a).leftAdjointUniq (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1}
      (terminalIsTerminal.isTerminalObj (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX))
        (⊤_ X.ProEt)))).hom.app P) = _
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.comp_homEquiv]
  change _ = c.homEquiv P _ (a.homEquiv _ _
    ((a.leftAdjointIdIso (pushforwardIso p hp X hX)).hom.app _))
  erw [← AlgebraicGeometry.FormalGeometry.Completion.AdjunctionCoherence.Construction.adjunction_id_adjoint a (pushforwardIso p hp X hX), Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  exact (AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.constantSheafAdj_unit_restrict (Scheme.ProEt.topology X)
    (terminalIsTerminal.isTerminalObj (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p hp X hX)) (⊤_ X.ProEt))
    terminalIsTerminal ((ProEtaleFst.ProEtaleFrobeniusSite.baseChangeIso p hp X hX).inv.app (⊤_ X.ProEt)) P).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtaleTo.ProEtaleFrobeniusSheaves
