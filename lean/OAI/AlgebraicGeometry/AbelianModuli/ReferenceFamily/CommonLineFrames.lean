import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.TensorTransitions

/-! # Common Line Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonLineFrames

noncomputable section

section

/-! Pairs of actual line bundles admit simultaneous local frames on
the same open sets. Their tensor frames have product transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}}

structure CommonLineFrame (M N : X.Modules) where
  domain : X.Opens
  leftFrame : M.restrict domain.ι ≅ HilbertConstruction.Line.Bundles.structureModule domain.toScheme
  rightFrame : N.restrict domain.ι ≅ HilbertConstruction.Line.Bundles.structureModule domain.toScheme

namespace CommonLineFrame

variable {M N : X.Modules}

def left (s : CommonLineFrame M N) : LineFrameAtlas.LocalLineFrame M := ⟨s.domain, s.leftFrame⟩
def right (s : CommonLineFrame M N) : LineFrameAtlas.LocalLineFrame N := ⟨s.domain, s.rightFrame⟩
def tensor (s : CommonLineFrame M N) : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) :=
  Local.TensorTransitions.localTensorFrame s.domain s.leftFrame s.rightFrame

end CommonLineFrame

theorem commonLineFrames_cover (L M : HilbertConstruction.Line.Bundles.LineBundle X) (x : X) :
    ∃ s : CommonLineFrame L.sheaf M.sheaf, x ∈ s.domain := by
  obtain ⟨a, ha⟩ := LineFrameAtlas.localLineFrames_cover L x
  obtain ⟨b, hb⟩ := LineFrameAtlas.localLineFrames_cover M x
  exact ⟨⟨a.domain ⊓ b.domain, DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization a.frame inf_le_left,
    DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization b.frame inf_le_right⟩, ha, hb⟩

variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L M : P.carrier.Modules}

theorem commonLineFrame_tensor_transition (s t : CommonLineFrame L M)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) (hs : p ∈ AnalyticFrameTransitions.frameAnalyticOpen P s.left)
    (ht : p ∈ AnalyticFrameTransitions.frameAnalyticOpen P t.left) :
    AnalyticFrameTransitions.framePointTransition P s.tensor t.tensor p hs ht =
      AnalyticFrameTransitions.framePointTransition P s.left t.left p hs ht * AnalyticFrameTransitions.framePointTransition P s.right t.right p hs ht :=
  Local.TensorTransitions.localTensorFrame_pointTransition s.domain t.domain s.leftFrame t.leftFrame s.rightFrame t.rightFrame p hs ht

end

/-! Simultaneous actual frames for a source line, a target line, and
the auxiliary tensor line, on covers inside prescribed tensor frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}}

structure TripleLineFrame (M N H : X.Modules) where
  domain : X.Opens
  sourceFrame : M.restrict domain.ι ≅ HilbertConstruction.Line.Bundles.structureModule domain.toScheme
  targetFrame : N.restrict domain.ι ≅ HilbertConstruction.Line.Bundles.structureModule domain.toScheme
  tensorFrame : H.restrict domain.ι ≅ HilbertConstruction.Line.Bundles.structureModule domain.toScheme

namespace TripleLineFrame

variable {M N H : X.Modules}

def source (s : TripleLineFrame M N H) : LineFrameAtlas.LocalLineFrame M := ⟨s.domain, s.sourceFrame⟩
def target (s : TripleLineFrame M N H) : LineFrameAtlas.LocalLineFrame N := ⟨s.domain, s.targetFrame⟩
def auxiliary (s : TripleLineFrame M N H) : LineFrameAtlas.LocalLineFrame H := ⟨s.domain, s.tensorFrame⟩
def tensorSource (s : TripleLineFrame M N H) : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M H) :=
  Local.TensorTransitions.localTensorFrame s.domain s.sourceFrame s.tensorFrame
def tensorTarget (s : TripleLineFrame M N H) : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule N H) :=
  Local.TensorTransitions.localTensorFrame s.domain s.targetFrame s.tensorFrame

def restrict (s : TripleLineFrame M N H) (U : X.Opens) (hU : U ≤ s.domain) : TripleLineFrame M N H where
  domain := U
  sourceFrame := DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization s.sourceFrame hU
  targetFrame := DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization s.targetFrame hU
  tensorFrame := DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization s.tensorFrame hU

end TripleLineFrame

theorem tripleLineFrames_cover (L K H : HilbertConstruction.Line.Bundles.LineBundle X) (x : X) :
    ∃ q : TripleLineFrame L.sheaf K.sheaf H.sheaf, x ∈ q.domain := by
  obtain ⟨a, ha⟩ := commonLineFrames_cover L K x
  obtain ⟨b, hb⟩ := LineFrameAtlas.localLineFrames_cover H x
  exact ⟨⟨a.domain ⊓ b.domain,
    DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization a.leftFrame inf_le_left, DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization a.rightFrame inf_le_left,
    DivisorClass.Chern.Line.Bundles.Construction.restrictTrivialization b.frame inf_le_right⟩, ha, hb⟩

def TensorMorphismFrameIndex {M N H : X.Modules}
    (r : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M H)) (s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule N H)) :=
  {q : TripleLineFrame M N H // q.domain ≤ r.domain ⊓ s.domain}

theorem tensorMorphismFrames_cover (L K H : HilbertConstruction.Line.Bundles.LineBundle X)
    (r : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule L.sheaf H.sheaf))
    (s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule K.sheaf H.sheaf)) (x : X)
    (hx : x ∈ r.domain ⊓ s.domain) :
    ∃ i : TensorMorphismFrameIndex r s, x ∈ i.val.domain := by
  obtain ⟨q, hq⟩ := tripleLineFrames_cover L K H x
  exact ⟨⟨q.restrict (q.domain ⊓ (r.domain ⊓ s.domain)) inf_le_left, inf_le_right⟩, hq, hx⟩

namespace TripleLineFrame

variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L K H : P.carrier.Modules}

theorem tensorSource_transition (s t : TripleLineFrame L K H) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hs : x ∈ AnalyticFrameTransitions.frameAnalyticOpen P s.source) (ht : x ∈ AnalyticFrameTransitions.frameAnalyticOpen P t.source) :
    AnalyticFrameTransitions.framePointTransition P s.tensorSource t.tensorSource x hs ht =
      AnalyticFrameTransitions.framePointTransition P s.source t.source x hs ht * AnalyticFrameTransitions.framePointTransition P s.auxiliary t.auxiliary x hs ht :=
  Local.TensorTransitions.localTensorFrame_pointTransition s.domain t.domain s.sourceFrame t.sourceFrame s.tensorFrame t.tensorFrame x hs ht

theorem tensorTarget_transition (s t : TripleLineFrame L K H) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hs : x ∈ AnalyticFrameTransitions.frameAnalyticOpen P s.target) (ht : x ∈ AnalyticFrameTransitions.frameAnalyticOpen P t.target) :
    AnalyticFrameTransitions.framePointTransition P s.tensorTarget t.tensorTarget x hs ht =
      AnalyticFrameTransitions.framePointTransition P s.target t.target x hs ht * AnalyticFrameTransitions.framePointTransition P s.auxiliary t.auxiliary x hs ht :=
  Local.TensorTransitions.localTensorFrame_pointTransition s.domain t.domain s.targetFrame t.targetFrame s.tensorFrame t.tensorFrame x hs ht

end TripleLineFrame

theorem tensorCoefficient_ratio_independent (a b h u v c d : ℂ)
    (ha : a ≠ 0) (hh : h ≠ 0) (hu : u ≠ 0) (he : a * c = d * b) :
    c * v / u = d * (v * (b * h)) / (u * (a * h)) := by
  apply (div_eq_div_iff hu (mul_ne_zero hu (mul_ne_zero ha hh))).mpr
  calc
    _ = (a * c) * (v * u * h) := by ring
    _ = (d * b) * (v * u * h) := congrArg (· * (v * u * h)) he
    _ = _ := by ring

theorem tensorCoefficient_ratio_anchors (a b u u' v v' c : ℂ)
    (ha : a ≠ 0) (hu' : u' ≠ 0) (hu : u = a * u') (hv : v = b * v') :
    a * (c * v / u) = (c * v' / u') * b := by
  rw [hu, hv]
  field_simp

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonLineFrames
