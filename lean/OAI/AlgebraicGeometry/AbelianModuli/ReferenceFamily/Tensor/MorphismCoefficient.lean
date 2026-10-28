import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonLineFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LineMorphismCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FrameClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

/-! # Morphism Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! Local tensor transport uses genuine holomorphic transition units
between the prescribed tensor frames and simultaneous algebraic frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K H : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    {r : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule L.sheaf H.sheaf)}
    {s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule K.sheaf H.sheaf)}

section

def CommonLineFrames.TensorMorphismFrameIndex.analyticOpen (i : CommonLineFrames.TensorMorphismFrameIndex r s) : Opens V.analyticSpace :=
  AnalyticFrameTransitions.frameAnalyticOpen V.presentation i.val.source

def CommonLineFrames.TensorMorphismFrameIndex.sourceGauge (i : CommonLineFrames.TensorMorphismFrameIndex r s) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := i.analyticOpen))ˣ :=
  Units.map (DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (E := V.analyticModel)
    (show i.analyticOpen ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓
      AnalyticFrameTransitions.frameAnalyticOpen V.presentation i.val.tensorSource from fun _ hx => ⟨(i.property hx).1, hx⟩)).toMonoidHom
    (Holomorphic.FrameClass.frameHolomorphicUnit V r i.val.tensorSource)

def CommonLineFrames.TensorMorphismFrameIndex.targetGauge (i : CommonLineFrames.TensorMorphismFrameIndex r s) :
    (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := i.analyticOpen))ˣ :=
  Units.map (DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (E := V.analyticModel)
    (show i.analyticOpen ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s ⊓
      AnalyticFrameTransitions.frameAnalyticOpen V.presentation i.val.tensorTarget from fun _ hx => ⟨(i.property hx).2, hx⟩)).toMonoidHom
    (Holomorphic.FrameClass.frameHolomorphicUnit V s i.val.tensorTarget)

theorem CommonLineFrames.TensorMorphismFrameIndex.sourceGauge_value (i : CommonLineFrames.TensorMorphismFrameIndex r s) (x : i.analyticOpen) :
    i.sourceGauge.val x = AnalyticFrameTransitions.framePointTransition V.presentation r i.val.tensorSource x.val
      (i.property x.property).1 x.property := rfl

theorem CommonLineFrames.TensorMorphismFrameIndex.targetGauge_value (i : CommonLineFrames.TensorMorphismFrameIndex r s) (x : i.analyticOpen) :
    i.targetGauge.val x = AnalyticFrameTransitions.framePointTransition V.presentation s i.val.tensorTarget x.val
      (i.property x.property).2 x.property := rfl

end

def Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorLocalCoefficient (D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K)
    (i : CommonLineFrames.TensorMorphismFrameIndex r s) : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel) (M := i.analyticOpen) :=
  DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction
    (show i.analyticOpen ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation i.val.source ⊓
      AnalyticFrameTransitions.frameAnalyticOpen V.presentation i.val.target from fun _ hx => ⟨hx, hx⟩)
    (D.coefficient i.val.source i.val.target) * i.targetGauge.val * (i.sourceGauge⁻¹).val

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorLocalCoefficient_value (D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K)
    (i : CommonLineFrames.TensorMorphismFrameIndex r s) (x : i.analyticOpen) :
    D.tensorLocalCoefficient i x = D.coefficient i.val.source i.val.target ⟨x.val, x.property, x.property⟩ *
      AnalyticFrameTransitions.framePointTransition V.presentation s i.val.tensorTarget x.val (i.property x.property).2 x.property /
        AnalyticFrameTransitions.framePointTransition V.presentation r i.val.tensorSource x.val (i.property x.property).1 x.property := by
  change D.coefficient i.val.source i.val.target ⟨x.val, x.property, x.property⟩ *
    i.targetGauge.val x * (i.sourceGauge⁻¹).val x = _
  rw [Holomorphic.GlobalGluing.holomorphicUnit_inverse_value V.analyticModel i.analyticOpen i.sourceGauge x,
    i.sourceGauge_value x, i.targetGauge_value x, div_eq_mul_inv]

end

section

/-! Local tensor coefficients are independent of all simultaneous
frame choices. The auxiliary frame transition cancels in both factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K H : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    {r : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule L.sheaf H.sheaf)}
    {s : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule K.sheaf H.sheaf)}

section

theorem CommonLineFrames.TensorMorphismFrameIndex.sourceGauge_change (i j : CommonLineFrames.TensorMorphismFrameIndex r s) (x : V.analyticSpace)
    (hi : x ∈ i.analyticOpen) (hj : x ∈ j.analyticOpen) :
    AnalyticFrameTransitions.framePointTransition V.presentation r j.val.tensorSource x (j.property hj).1 hj =
      AnalyticFrameTransitions.framePointTransition V.presentation r i.val.tensorSource x (i.property hi).1 hi *
        (AnalyticFrameTransitions.framePointTransition V.presentation i.val.source j.val.source x hi hj *
          AnalyticFrameTransitions.framePointTransition V.presentation i.val.auxiliary j.val.auxiliary x hi hj) :=
  (AnalyticFrameTransitions.framePointTransition_cocycle V.presentation r i.val.tensorSource j.val.tensorSource
    x (i.property hi).1 hi hj).symm.trans
      (congrArg (AnalyticFrameTransitions.framePointTransition V.presentation r i.val.tensorSource x (i.property hi).1 hi * ·)
        (i.val.tensorSource_transition (P := V.presentation) j.val x hi hj))

theorem CommonLineFrames.TensorMorphismFrameIndex.targetGauge_change (i j : CommonLineFrames.TensorMorphismFrameIndex r s) (x : V.analyticSpace)
    (hi : x ∈ i.analyticOpen) (hj : x ∈ j.analyticOpen) :
    AnalyticFrameTransitions.framePointTransition V.presentation s j.val.tensorTarget x (j.property hj).2 hj =
      AnalyticFrameTransitions.framePointTransition V.presentation s i.val.tensorTarget x (i.property hi).2 hi *
        (AnalyticFrameTransitions.framePointTransition V.presentation i.val.target j.val.target x hi hj *
          AnalyticFrameTransitions.framePointTransition V.presentation i.val.auxiliary j.val.auxiliary x hi hj) :=
  (AnalyticFrameTransitions.framePointTransition_cocycle V.presentation s i.val.tensorTarget j.val.tensorTarget
    x (i.property hi).2 hi hj).symm.trans
      (congrArg (AnalyticFrameTransitions.framePointTransition V.presentation s i.val.tensorTarget x (i.property hi).2 hi * ·)
        (i.val.tensorTarget_transition (P := V.presentation) j.val x hi hj))

end

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorLocalCoefficient_compatible (D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K)
    (i j : CommonLineFrames.TensorMorphismFrameIndex r s) (x : V.analyticSpace)
    (hi : x ∈ i.analyticOpen) (hj : x ∈ j.analyticOpen) :
    D.tensorLocalCoefficient i ⟨x, hi⟩ = D.tensorLocalCoefficient j ⟨x, hj⟩ := by
  rw [D.tensorLocalCoefficient_value i ⟨x, hi⟩, D.tensorLocalCoefficient_value j ⟨x, hj⟩,
    i.sourceGauge_change j x hi hj, i.targetGauge_change j x hi hj]
  exact CommonLineFrames.tensorCoefficient_ratio_independent _ _ _ _ _ _ _
    (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation i.val.source j.val.source ⟨x, hi, hj⟩)
    (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation i.val.auxiliary j.val.auxiliary ⟨x, hi, hj⟩)
    (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation r i.val.tensorSource ⟨x, (i.property hi).1, hi⟩)
    (D.frame_change i.val.source j.val.source i.val.target j.val.target x ⟨hi, hi⟩ ⟨hj, hj⟩)

end

section

/-! The compatible local tensor coefficients glue on every prescribed
pair of actual tensor-frame domains, without a global auxiliary frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    (D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K) (H : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    (r : LineFrameAtlas.LocalLineFrame (L.tensor H).sheaf) (s : LineFrameAtlas.LocalLineFrame (K.tensor H).sheaf)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.exists_tensorCoefficient :
    ∃ a : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := (AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s : Opens V.analyticSpace)),
      ∀ (i : CommonLineFrames.TensorMorphismFrameIndex r s) (x : i.analyticOpen),
        a ⟨x.val, i.property x.property⟩ = D.tensorLocalCoefficient i x := by
  let U := fun i : CommonLineFrames.TensorMorphismFrameIndex r s => i.analyticOpen
  have hcover : AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s ≤ iSup U := by
    intro x hx
    obtain ⟨i, hi⟩ := CommonLineFrames.tensorMorphismFrames_cover L K H r s (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x) hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨a, ha⟩ := DivisorClass.Chern.Holomorphic.FunctionGluing.exists_holomorphicFunction_glue U (D.tensorLocalCoefficient)
    (D.tensorLocalCoefficient_compatible)
  refine ⟨DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction hcover a, ?_⟩
  intro i x
  exact ha i x

def Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorCoefficient : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
    (M := (AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s : Opens V.analyticSpace)) :=
  Classical.choose (D.exists_tensorCoefficient H r s)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorCoefficient_value (i : CommonLineFrames.TensorMorphismFrameIndex r s) (x : i.analyticOpen) :
    D.tensorCoefficient H r s ⟨x.val, i.property x.property⟩ = D.tensorLocalCoefficient i x :=
  Classical.choose_spec (D.exists_tensorCoefficient H r s) i x

end

/-! Glued tensor coefficients satisfy the native frame-change law.
In induced tensor frames they recover exactly the original coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FunctionGluing

theorem Tensor.MorphismCoefficient.framePointTransition_self (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {M : P.carrier.Modules}
    (r : LineFrameAtlas.LocalLineFrame M) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) (hx : x ∈ AnalyticFrameTransitions.frameAnalyticOpen P r) :
    AnalyticFrameTransitions.framePointTransition P r r x hx hx = 1 := by
  apply mul_left_cancel₀ (AnalyticFrameTransitions.frameTransitionPair_ne_zero P r r ⟨x, hx, hx⟩)
  exact (AnalyticFrameTransitions.framePointTransition_cocycle P r r r x hx hx hx).trans (mul_one _).symm

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    (D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K) (H : HilbertConstruction.Line.Bundles.LineBundle V.carrier)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorCoefficient_frame_change (r₀ r₁ : LineFrameAtlas.LocalLineFrame (L.tensor H).sheaf)
    (s₀ s₁ : LineFrameAtlas.LocalLineFrame (K.tensor H).sheaf) (x : V.analyticSpace)
    (h₀ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₀ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₀)
    (h₁ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₁ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₁) :
    AnalyticFrameTransitions.framePointTransition V.presentation r₀ r₁ x h₀.1 h₁.1 * D.tensorCoefficient H r₀ s₀ ⟨x, h₀⟩ =
      D.tensorCoefficient H r₁ s₁ ⟨x, h₁⟩ * AnalyticFrameTransitions.framePointTransition V.presentation s₀ s₁ x h₀.2 h₁.2 := by
  obtain ⟨q, hq⟩ := CommonLineFrames.tripleLineFrames_cover L K H (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)
  let U := q.domain ⊓ ((r₀.domain ⊓ s₀.domain) ⊓ (r₁.domain ⊓ s₁.domain))
  let q' := q.restrict U inf_le_left
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ q'.domain := ⟨hq, h₀, h₁⟩
  let i₀ : CommonLineFrames.TensorMorphismFrameIndex r₀ s₀ := ⟨q', inf_le_right.trans inf_le_left⟩
  let i₁ : CommonLineFrames.TensorMorphismFrameIndex r₁ s₁ := ⟨q', inf_le_right.trans inf_le_right⟩
  rw [D.tensorCoefficient_value H r₀ s₀ i₀ ⟨x, hx⟩, D.tensorCoefficient_value H r₁ s₁ i₁ ⟨x, hx⟩,
    D.tensorLocalCoefficient_value i₀ ⟨x, hx⟩, D.tensorLocalCoefficient_value i₁ ⟨x, hx⟩]
  exact CommonLineFrames.tensorCoefficient_ratio_anchors _ _ _ _ _ _ _
    (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation r₀ r₁ ⟨x, h₀.1, h₁.1⟩)
    (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation r₁ q'.tensorSource ⟨x, h₁.1, hx⟩)
    (AnalyticFrameTransitions.framePointTransition_cocycle V.presentation r₀ r₁ q'.tensorSource x h₀.1 h₁.1 hx).symm
    (AnalyticFrameTransitions.framePointTransition_cocycle V.presentation s₀ s₁ q'.tensorTarget x h₀.2 h₁.2 hx).symm

def Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensor : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V (L.tensor H) (K.tensor H) where
  coefficient := D.tensorCoefficient H
  frame_change := D.tensorCoefficient_frame_change H

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensor_induced_coefficient (q : CommonLineFrames.TripleLineFrame L.sheaf K.sheaf H.sheaf)
    (x : AnalyticFrameTransitions.frameAnalyticOpen V.presentation q.source) :
    (D.tensor H).coefficient q.tensorSource q.tensorTarget ⟨x.val, x.property, x.property⟩ =
      D.coefficient q.source q.target ⟨x.val, x.property, x.property⟩ := by
  let i : CommonLineFrames.TensorMorphismFrameIndex q.tensorSource q.tensorTarget := ⟨q, le_inf le_rfl le_rfl⟩
  have h := D.tensorCoefficient_value H q.tensorSource q.tensorTarget i x
  refine h.trans ((D.tensorLocalCoefficient_value i x).trans ?_)
  rw [Tensor.MorphismCoefficient.framePointTransition_self V.presentation q.tensorTarget x.val x.property,
    Tensor.MorphismCoefficient.framePointTransition_self V.presentation q.tensorSource x.val x.property, mul_one, div_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
