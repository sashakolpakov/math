import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TransitionCocycle

/-! # Cocycle Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CocyclePullback

noncomputable section

/-! Regular transition cocycles pull back by the actual scheme maps
on sections, including their original overlap restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u} (U : I → Y.Opens)

def regularTransitionPullback (r : TransitionCocycle.RegularTransitionCoefficients U) :
    TransitionCocycle.RegularTransitionCoefficients (fun i => f ⁻¹ᵁ U i) :=
  fun i j => Units.map (f.app (U i ⊓ U j)).hom.toMonoidHom (r i j)

theorem regularUnitPullback_restrict {V W : Y.Opens} (h : W ≤ V) (a : Γ(Y, V)ˣ) :
    Units.map (f.app W).hom.toMonoidHom (UnitRestrictions.regularUnitRestrict Y h a) =
      UnitRestrictions.regularUnitRestrict X (f.preimage_mono h) (Units.map (f.app V).hom.toMonoidHom a) := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) a.val

theorem regularTransitionPullback_on (r : TransitionCocycle.RegularTransitionCoefficients U) (i j : I)
    (W : Y.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    TransitionCocycle.regularTransitionOn (fun i => f ⁻¹ᵁ U i) (regularTransitionPullback f U r) i j (f ⁻¹ᵁ W)
      (f.preimage_mono hi) (f.preimage_mono hj) =
        Units.map (f.app W).hom.toMonoidHom (TransitionCocycle.regularTransitionOn U r i j W hi hj) :=
  (regularUnitPullback_restrict f (le_inf hi hj) (r i j)).symm

theorem regularTransitionPullback_cocycle (r : TransitionCocycle.RegularTransitionCoefficients U)
    (hr : TransitionCocycle.RegularTransitionCocycle U r) :
    TransitionCocycle.RegularTransitionCocycle (fun i => f ⁻¹ᵁ U i) (regularTransitionPullback f U r) := by
  intro i j k
  have h := congrArg (Units.map (f.app ((U i ⊓ U j) ⊓ U k)).hom.toMonoidHom) (hr i j k)
  rw [map_mul, ← regularTransitionPullback_on, ← regularTransitionPullback_on,
    ← regularTransitionPullback_on] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CocyclePullback
