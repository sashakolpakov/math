import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineTangentLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TopSectionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateSectionMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

/-! # Frame Coordinate Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.FrameCoordinateUnits

noncomputable section

/-! Original line-frame transition units in the coordinate rings of
actual affine family opens. Their products and restrictions are the
original frame cocycle, transported through the native top-section iso. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (.of R)))

def familyAffineSectionEquiv (V : X.left.affineOpens) :
    AffineTangentLifts.familyAffineRing R X V ≃+* Γ(X.left, V.1) := V.1.topIso.commRingCatIsoToRingEquiv

theorem familyAffineSectionEquiv_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (a : AffineTangentLifts.familyAffineRing R X W) :
    familyAffineSectionEquiv R X V (Affine.OpenDiagram.familyAffineCoordinateMap R X h a) =
      X.left.presheaf.map (homOfLE h).op (familyAffineSectionEquiv R X W a) := by
  have he := @Affine.CoordinateSectionMap.affineCoordinateMap_apply R inferInstance
    ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V) ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj W)
    inferInstance inferInstance (Affine.OpenDiagram.familyOpenMap X h) a
  exact (congrArg (familyAffineSectionEquiv R X V) he).trans (Open.TopSectionNaturality.openTopSection_restrict h a)

variable {I : Type} (U : I → X.left.Opens) (D : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions U)

def familyFrameCoordinateUnit (V : X.left.affineOpens) (i j : I) (hi : V.1 ≤ U i) (hj : V.1 ≤ U j) :
    (AffineTangentLifts.familyAffineRing R X V)ˣ :=
  Units.map (familyAffineSectionEquiv R X V).symm.toMonoidHom (D.value V.1 i j hi hj)

theorem familyFrameCoordinateUnit_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (i j : I) (hi : W.1 ≤ U i) (hj : W.1 ≤ U j) :
    Units.map (Affine.OpenDiagram.familyAffineCoordinateMap R X h).toMonoidHom (familyFrameCoordinateUnit R X U D W i j hi hj) =
      familyFrameCoordinateUnit R X U D V i j (h.trans hi) (h.trans hj) := by
  apply Units.ext
  apply (familyAffineSectionEquiv R X V).injective
  change familyAffineSectionEquiv R X V (Affine.OpenDiagram.familyAffineCoordinateMap R X h
      ((familyAffineSectionEquiv R X W).symm (D.value W.1 i j hi hj).val)) =
    familyAffineSectionEquiv R X V
      ((familyAffineSectionEquiv R X V).symm (D.value V.1 i j (h.trans hi) (h.trans hj)).val)
  rw [familyAffineSectionEquiv_restrict, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact D.restrict W.1 V.1 h i j hi hj

theorem familyFrameCoordinateUnit_cocycle (V : X.left.affineOpens) (i j l : I)
    (hi : V.1 ≤ U i) (hj : V.1 ≤ U j) (hl : V.1 ≤ U l) :
    familyFrameCoordinateUnit R X U D V i j hi hj * familyFrameCoordinateUnit R X U D V j l hj hl =
      familyFrameCoordinateUnit R X U D V i l hi hl := by
  unfold familyFrameCoordinateUnit
  rw [← map_mul, D.comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.FrameCoordinateUnits
