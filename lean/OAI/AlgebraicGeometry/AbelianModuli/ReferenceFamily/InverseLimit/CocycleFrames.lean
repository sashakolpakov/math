import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquareFrameTransitionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CechFrame

/-! # Cocycle Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleFrames

noncomputable section

/-! The descended cocycle line has actual pullback frames on the
original limit opens, with exactly the original cone-pulled units. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {I : Type} [Category.{0} I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    {i : I} {J : Type} (U : J → (D.obj i).Opens) (k : Over i)
    (q : Open.TransitionCocycle.OpenTransitionCoefficients (fun a => D.map k.hom ⁻¹ᵁ U a))
    (hq : Open.TransitionCocycle.OpenTransitionCocycle (fun a => D.map k.hom ⁻¹ᵁ U a) q)

def inverseLimitCocycleFrame (a : J) :
    LineFrameAtlas.LocalLineFrame ((Scheme.Modules.pullback (c.π.app k.left)).obj
      (Cech.LineModule.cechLineModule (fun a => D.map k.hom ⁻¹ᵁ U a)
        (Regular.CechGenerator.regularCechCoefficients _ (Open.TransitionCocycle.regularCoefficientsOfOpen _ q)))) :=
  Dual.TensorCechCoefficients.localFrameFromPullback (c.π.app i ⁻¹ᵁ U a)
    (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (c.π.app k.left) (c.π.app i ⁻¹ᵁ U a).ι
      (D.map k.hom ⁻¹ᵁ U a).ι ((opensCone D c i (U a)).π.app k)
      (OpenRestriction.opensConeProjection_ι D c i (U a) k) _
      (Regular.CechFrame.regularCechNativeFrame _ (Open.TransitionCocycle.regularCoefficientsOfOpen _ q)
        ((Open.TransitionCocycle.regularCoefficientsOfOpen_cocycle_iff _ q).mpr hq) a).pullbackFrame)

theorem inverseLimitCocycleFrame_transition (a b : J) (W : (D.obj i).Opens)
    (ha : W ≤ U a) (hb : W ≤ U b) :
    (inverseLimitCocycleFrame D c U k q hq a).transition (inverseLimitCocycleFrame D c U k q hq b)
      (c.π.app i ⁻¹ᵁ W) ((c.π.app i).preimage_mono ha) ((c.π.app i).preimage_mono hb) =
    Open.UnitCoordinates.openUnitToRegular (c.π.app i ⁻¹ᵁ W)
      (Open.TransitionCocycle.openTransitionOn (fun a => c.π.app i ⁻¹ᵁ U a) (CocycleMaps.openCoefficientsConePullback D c U k q) b a
        (c.π.app i ⁻¹ᵁ W) ((c.π.app i).preimage_mono hb) ((c.π.app i).preimage_mono ha)) := by
  let V := fun a => D.map k.hom ⁻¹ᵁ U a
  let r := Open.TransitionCocycle.regularCoefficientsOfOpen V q
  let hr := (Open.TransitionCocycle.regularCoefficientsOfOpen_cocycle_iff V q).mpr hq
  let M := Cech.LineModule.cechLineModule V (Regular.CechGenerator.regularCechCoefficients V r)
  let p := fun Z => (opensCone D c i Z).π.app k
  have h₁ := SquareFrameTransitionRecovery.squarePulledFrame_transition (c.π.app k.left) M (V a) (V b) (D.map k.hom ⁻¹ᵁ W)
    (c.π.app i ⁻¹ᵁ U a) (c.π.app i ⁻¹ᵁ U b) (c.π.app i ⁻¹ᵁ W)
    ((D.map k.hom).preimage_mono ha) ((D.map k.hom).preimage_mono hb)
    ((c.π.app i).preimage_mono ha) ((c.π.app i).preimage_mono hb) (p (U a)) (p (U b)) (p W)
    (OpenRestriction.opensConeProjection_ι D c i (U a) k) (OpenRestriction.opensConeProjection_ι D c i (U b) k)
    (OpenRestriction.opensConeProjection_ι D c i W k)
    (RestrictedOpenUnitNaturality.openMaps_restriction (c.π.app k.left) ((D.map k.hom).preimage_mono ha)
      ((c.π.app i).preimage_mono ha) (p (U a)) (p W)
      (OpenRestriction.opensConeProjection_ι D c i (U a) k) (OpenRestriction.opensConeProjection_ι D c i W k))
    (RestrictedOpenUnitNaturality.openMaps_restriction (c.π.app k.left) ((D.map k.hom).preimage_mono hb)
      ((c.π.app i).preimage_mono hb) (p (U b)) (p W)
      (OpenRestriction.opensConeProjection_ι D c i (U b) k) (OpenRestriction.opensConeProjection_ι D c i W k))
    (Regular.CechFrame.regularCechNativeFrame V r hr a).pullbackFrame (Regular.CechFrame.regularCechNativeFrame V r hr b).pullbackFrame
  have h₂ := LineFrameAtlas.LocalLineFrame.transition_congr
    (LineFrameAtlas.LocalLineFrame.fromPullbackFrame (Regular.CechFrame.regularCechNativeFrame V r hr a))
    (LineFrameAtlas.LocalLineFrame.fromPullbackFrame (Regular.CechFrame.regularCechNativeFrame V r hr b)) (D.map k.hom ⁻¹ᵁ W)
    ((D.map k.hom).preimage_mono ha) ((D.map k.hom).preimage_mono hb)
    ((D.map k.hom).preimage_mono ha) ((D.map k.hom).preimage_mono hb)
  have h₃ := Regular.CechFrame.regularCechNativeFrame_transition V r hr a b (D.map k.hom ⁻¹ᵁ W)
    ((D.map k.hom).preimage_mono ha) ((D.map k.hom).preimage_mono hb)
  have h₄ := Open.TransitionCocycle.regularCoefficientsOfOpen_on V q b a (D.map k.hom ⁻¹ᵁ W)
    ((D.map k.hom).preimage_mono hb) ((D.map k.hom).preimage_mono ha)
  have h₅ := (congrArg (Open.UnitCoordinates.regularUnitToOpen (D.map k.hom ⁻¹ᵁ W))
    (h₂.trans (h₃.trans h₄))).trans (Open.UnitCoordinates.regularUnitToOpen_toRegular _ _)
  exact h₁.trans ((congrArg (fun u => Open.UnitCoordinates.openUnitToRegular (c.π.app i ⁻¹ᵁ W)
    (Units.map (p W).appTop.hom.toMonoidHom u)) h₅).trans
      (congrArg (Open.UnitCoordinates.openUnitToRegular (c.π.app i ⁻¹ᵁ W)) (CocycleMaps.openTransitionOn_cone D c U k q b a W hb ha)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.CocycleFrames
