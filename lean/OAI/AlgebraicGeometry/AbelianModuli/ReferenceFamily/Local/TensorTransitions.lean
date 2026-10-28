import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions

/-! # Tensor Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.TensorTransitions

noncomputable section

/-! Tensor frames over a common parent open have product transition
units on every overlap, even when the two parent opens differ. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {M N : X.Modules}

def localTensorFrame (U : X.Opens) (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (f : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) where
  domain := U
  frame := Tensor.FrameCoordinates.tensorFrameOnDomain M N U e f

theorem localTensorFrame_transition (U V W : X.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) (e' : M.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme)
    (f : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) (f' : N.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme) :
    (localTensorFrame U e f).transition (localTensorFrame V e' f') W hU hV =
      (LineFrameAtlas.LocalLineFrame.mk U e).transition (LineFrameAtlas.LocalLineFrame.mk V e') W hU hV *
        (LineFrameAtlas.LocalLineFrame.mk U f).transition (LineFrameAtlas.LocalLineFrame.mk V f') W hU hV :=
  Tensor.FrameTransitions.frameTransitionUnit_bilinear ((SheafTensorMaps.tensorBilinear M N).app W) _ _ _ _ _ _
    (Tensor.FrameCoordinates.tensorFrameOnOpen_apply M N U e f W hU) (Tensor.FrameCoordinates.tensorFrameOnOpen_apply M N V e' f' W hV)

variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L Q : P.carrier.Modules}

theorem localTensorFrame_pointTransition (U V : P.carrier.Opens)
    (e : L.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) (e' : L.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme)
    (f : Q.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) (f' : Q.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) (hU : p ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P U) (hV : p ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P V) :
    AnalyticFrameTransitions.framePointTransition P (localTensorFrame U e f) (localTensorFrame V e' f') p hU hV =
      AnalyticFrameTransitions.framePointTransition P (LineFrameAtlas.LocalLineFrame.mk U e) (LineFrameAtlas.LocalLineFrame.mk V e') p hU hV *
        AnalyticFrameTransitions.framePointTransition P (LineFrameAtlas.LocalLineFrame.mk U f) (LineFrameAtlas.LocalLineFrame.mk V f') p hU hV := by
  let q : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P (U ⊓ V) := ⟨p, hU, hV⟩
  have h := congrArg (fun u : Γ(P.carrier, U ⊓ V)ˣ =>
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (U ⊓ V) (u : Γ(P.carrier, U ⊓ V)) q)
      (localTensorFrame_transition U V (U ⊓ V) inf_le_left inf_le_right e e' f f')
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (U ⊓ V) _ q = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (U ⊓ V)
    (((LineFrameAtlas.LocalLineFrame.mk U e).transition (LineFrameAtlas.LocalLineFrame.mk V e') (U ⊓ V) inf_le_left inf_le_right :
      Γ(P.carrier, U ⊓ V)) *
    ((LineFrameAtlas.LocalLineFrame.mk U f).transition (LineFrameAtlas.LocalLineFrame.mk V f') (U ⊓ V) inf_le_left inf_le_right :
      Γ(P.carrier, U ⊓ V))) q at h
  rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, ← AnalyticFrameTransitions.framePointTransition_restrict,
    ← AnalyticFrameTransitions.framePointTransition_restrict] at h
  exact (AnalyticFrameTransitions.framePointTransition_restrict P (localTensorFrame U e f) (localTensorFrame V e' f')
    (U ⊓ V) inf_le_left inf_le_right q).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.TensorTransitions
