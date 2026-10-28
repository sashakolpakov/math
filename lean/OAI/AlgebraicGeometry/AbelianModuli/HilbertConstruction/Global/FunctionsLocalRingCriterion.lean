import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RingPullbackMapDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsFromAffineFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedFamilyFiberConnectedness

/-! # Functions Local Ring Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRingCriterion

noncomputable section

/-! A section and global-function constancy after all local-ring base changes imply global-function constancy over an arbitrary base scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affineMap_eq_of_localRingConstants {X S Y : Scheme.{u}} [IsAffine Y]
    (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 _)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (b : Spec (.of A) ⟶ S),
      IsIso (pullback.snd p b).appTop) (f : X ⟶ Y) : f = p ≫ x ≫ f := by
  apply Local.RingPullbackMapDetection.schemeMap_eq_of_localRingPullbacks p
  intro A _ _ b
  have := h A b
  let σ := PointedFamilyFiberConnectedness.schemeSectionBaseChange p x hx b
  have hσ : σ ≫ pullback.snd p b = 𝟙 _ := PointedFamilyFiberConnectedness.schemeSectionBaseChange_section p x hx b
  have e := FunctionsMapRigidity.affineMap_eq_of_globalFunctions_iso (pullback.snd p b) σ hσ (pullback.fst p b ≫ f)
  have hfst : σ ≫ pullback.fst p b = b ≫ x := pullback.lift_fst _ _ _
  rw [← Category.assoc σ, hfst, Category.assoc b, ← pullback.condition_assoc] at e
  exact e

theorem globalFunctions_isIso_of_localRingConstants {X S : Scheme.{u}}
    (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 _)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (b : Spec (.of A) ⟶ S),
      IsIso (pullback.snd p b).appTop) : IsIso p.appTop :=
  FunctionsFromAffineFactorization.globalFunctions_isIso_of_affinization_factorization p x hx
    (affineMap_eq_of_localRingConstants p x hx h X.toSpecΓ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRingCriterion
