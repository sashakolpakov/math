import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRingCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.GlobalFunctions

/-! # Global Functions Local Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GlobalFunctionsLocalCriterion

noncomputable section

/-! Global-function constancy on all local-ring tests implies constancy on every Cartesian base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem universal_globalFunctions_isIso_of_localRingConstants
    {X S T Y : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 _)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (c : Spec (.of A) ⟶ S),
      IsIso (pullback.snd p c).appTop)
    {a : Y ⟶ X} {b : Y ⟶ T} {c : T ⟶ S} (H : IsPullback a b p c) :
    IsIso b.appTop := by
  let σ := PointedFamilyFiberConnectedness.schemeSectionBaseChange p x hx c ≫ H.isoPullback.inv
  have hσ : σ ≫ b = 𝟙 _ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => PointedFamilyFiberConnectedness.schemeSectionBaseChange p x hx c ≫ f) H.isoPullback_inv_snd).trans
        (PointedFamilyFiberConnectedness.schemeSectionBaseChange_section p x hx c))
  apply Global.FunctionsLocalRingCriterion.globalFunctions_isIso_of_localRingConstants b σ hσ
  intro A _ _ s
  have H' : IsPullback (pullback.fst b s ≫ a) (pullback.snd b s) p (s ≫ c) :=
    (IsPullback.of_hasPullback b s).paste_horiz H
  exact (Cartesian.GlobalFunctions.cartesian_globalFunctions_isIso_iff H').mpr (h A (s ≫ c))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.GlobalFunctionsLocalCriterion
