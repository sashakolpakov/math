import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.AdjunctionCoherence

/-! # Pullback Coherence -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction

noncomputable section

/-!
# Completion: identity and composition comparisons for pro-étale inverse image

The comparisons are induced by scheme base change and adjunction. Their
direction records the contravariance of the eventual cohomology action.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Scheme.{u}}

attribute [local instance] ProetalePullback.Construction.weaklyEtale_composition ProetalePullback.Construction.weaklyEtale_hasPullbacksAlong
  ProetalePullback.Construction.weaklyEtale_baseChangeAlong

/-- Base change by a composite, with the order reversed. -/
def proEtBaseChangeCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ProetalePullback.Construction.proEtBaseChange (f ≫ g) ≅ ProetalePullback.Construction.proEtBaseChange g ⋙ ProetalePullback.Construction.proEtBaseChange f :=
  MorphismProperty.Over.pullbackComp f g

/-- Base change by the identity is canonically the identity on the site. -/
def proEtBaseChangeIdIso (X : Scheme.{u}) : ProetalePullback.Construction.proEtBaseChange (𝟙 X) ≅ 𝟭 X.ProEt :=
  NatIso.ofComponents (fun U =>
    MorphismProperty.Over.isoMk
      { hom := pullback.fst U.hom (𝟙 X)
        inv := pullback.lift (𝟙 U.left) U.hom (by simp)
        hom_inv_id := by apply pullback.hom_ext <;> simp [pullback.condition]
        inv_hom_id := by simp }
      (by
        change pullback.fst U.hom (𝟙 X) ≫ U.hom = pullback.snd U.hom (𝟙 X)
        simpa using (pullback.condition (f := U.hom) (g := 𝟙 X))))
    (fun _ => by apply MorphismProperty.Over.Hom.ext; exact pullback.lift_fst _ _ _)

/-- Direct-image composition comparison arising from base change. -/
def proEtSheafPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) ⋙
    (ProetalePullback.Construction.proEtBaseChange g).sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) ≅
    (ProetalePullback.Construction.proEtBaseChange (f ≫ g)).sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Z) (Scheme.ProEt.topology X) :=
  Functor.sheafPushforwardContinuousComp' (proEtBaseChangeCompIso f g).symm _ _ _ _

/-- Inverse image of a composite is the composite of inverse images. -/
def proEtSheafPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ProetalePullback.Construction.proEtSheafPullback g ⋙ ProetalePullback.Construction.proEtSheafPullback f ≅ ProetalePullback.Construction.proEtSheafPullback (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    ((ProetalePullback.Construction.proEtBaseChange g).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((ProetalePullback.Construction.proEtBaseChange (f ≫ g)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (proEtSheafPushforwardCompIso f g)

/-- Identity direct image is the identity on sheaves. -/
def proEtSheafPushforwardIdIso (X : Scheme.{u}) :
    (ProetalePullback.Construction.proEtBaseChange (𝟙 X)).sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (proEtBaseChangeIdIso X) _ _

/-- Identity inverse image is the identity on sheaves. -/
def proEtSheafPullbackIdIso (X : Scheme.{u}) : ProetalePullback.Construction.proEtSheafPullback (𝟙 X) ≅ 𝟭 _ :=
  Adjunction.leftAdjointIdIso
    ((ProetalePullback.Construction.proEtBaseChange (𝟙 X)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (proEtSheafPushforwardIdIso X)

/-- The coefficient maps respect composition of scheme morphisms. -/
theorem proEtCoefficientToPushforward_comp (ℓ : ℕ) [Fact ℓ.Prime]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ProetalePullback.Construction.proEtCoefficientToPushforward ℓ (f ≫ g) =
      ProetalePullback.Construction.proEtCoefficientToPushforward ℓ g ≫
        ((ProetalePullback.Construction.proEtBaseChange g).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)).map
            (ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f) ≫
        (proEtSheafPushforwardCompIso f g).hom.app (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) := by
  ext U s
  change ULift.{u + 1} (ContinuousMap U.unop.left (ℤ_[ℓ])) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change s.down ((pullback.fst U.unop.hom (f ≫ g)) x) =
    s.down ((pullback.fst U.unop.hom g)
      ((pullback.fst (pullback.snd U.unop.hom g) f)
        (((proEtBaseChangeCompIso f g).hom.app U.unop).left x)))
  exact congrArg (fun h : pullback U.unop.hom (f ≫ g) ⟶ U.unop.left => s.down (h x))
    (MorphismProperty.Over.pullbackComp_left_fst_fst f g U.unop).symm

/-- The coefficient map for the identity agrees with the canonical comparison. -/
theorem proEtCoefficientToPushforward_id (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    ProetalePullback.Construction.proEtCoefficientToPushforward ℓ (𝟙 X) ≫
      (proEtSheafPushforwardIdIso X).hom.app (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) = 𝟙 _ := by
  ext U s
  change ULift.{u + 1} (ContinuousMap U.unop.left (ℤ_[ℓ])) at s
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change s.down ((pullback.fst U.unop.hom (𝟙 X))
    (((proEtBaseChangeIdIso X).inv.app U.unop).left x)) = s.down x
  have h : ((proEtBaseChangeIdIso X).inv.app U.unop).left ≫
      pullback.fst U.unop.hom (𝟙 X) = 𝟙 U.unop.left := by
    exact congrArg (fun f => f.left) ((proEtBaseChangeIdIso X).inv_hom_id_app U.unop)
  exact congrArg (fun f : U.unop.left ⟶ U.unop.left => s.down (f x)) h

/-- Composition of the adjoint coefficient maps, with the necessary comparison. -/
theorem proEtCoefficientPullback_comp (ℓ : ℕ) [Fact ℓ.Prime]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (proEtSheafPullbackCompIso f g).hom.app (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Z) ≫
      ProetalePullback.Construction.proEtCoefficientPullback ℓ (f ≫ g) =
        (ProetalePullback.Construction.proEtSheafPullback f).map (ProetalePullback.Construction.proEtCoefficientPullback ℓ g) ≫
          ProetalePullback.Construction.proEtCoefficientPullback ℓ f := by
  unfold ProetalePullback.Construction.proEtCoefficientPullback
  rw [proEtCoefficientToPushforward_comp]
  exact AdjunctionCoherence.Construction.adjunction_comp_adjoint
    ((ProetalePullback.Construction.proEtBaseChange g).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    ((ProetalePullback.Construction.proEtBaseChange (f ≫ g)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (proEtSheafPushforwardCompIso f g)
    (ProetalePullback.Construction.proEtCoefficientToPushforward ℓ g) (ProetalePullback.Construction.proEtCoefficientToPushforward ℓ f)

/-- The adjoint coefficient map for the identity is the identity comparison. -/
theorem proEtCoefficientPullback_id (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    ProetalePullback.Construction.proEtCoefficientPullback ℓ (𝟙 X) =
      (proEtSheafPullbackIdIso X).hom.app (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) := by
  have h : ProetalePullback.Construction.proEtCoefficientToPushforward ℓ (𝟙 X) =
      (proEtSheafPushforwardIdIso X).inv.app (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X) := by
    rw [← cancel_mono ((proEtSheafPushforwardIdIso X).hom.app
      (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X)), proEtCoefficientToPushforward_id,
      Iso.inv_hom_id_app]
    rfl
  unfold ProetalePullback.Construction.proEtCoefficientPullback
  rw [h]
  exact AdjunctionCoherence.Construction.adjunction_id_adjoint
    ((ProetalePullback.Construction.proEtBaseChange (𝟙 X)).sheafAdjunctionContinuous Ab.{u + 1} _ _)
    (proEtSheafPushforwardIdIso X) (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PullbackCoherence.Construction
