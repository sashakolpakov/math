import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameUnitCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonLineFrames

/-! # Holomorphic Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTensor

noncomputable section

/-! The actual native holomorphic class adds on algebraic tensor
products, by the regular transition units of common sheaf frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance nativeHolomorphicTensor_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of V.analyticSpace) (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace) 1

theorem nativeHolomorphicLineClass_tensor (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) :
    HolomorphicLineClass.nativeHolomorphicLineClass V (L.tensor K) = HolomorphicLineClass.nativeHolomorphicLineClass V L + HolomorphicLineClass.nativeHolomorphicLineClass V K := by
  let I := CommonLineFrames.CommonLineFrame L.sheaf K.sheaf
  let U (i : I) := AnalyticFrameTransitions.frameAnalyticOpen V.presentation i.left
  have hU : ∀ p : V.analyticSpace, ∃ i, p ∈ U i := by
    intro p
    obtain ⟨i, hi⟩ := CommonLineFrames.commonLineFrames_cover L K (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)
    exact ⟨i, hi⟩
  let S := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace
  let T := TopCat.of V.analyticSpace
  let : AddCommGroup (CategoryTheory.Sheaf.H S 1) := Cech.Add.cechClassAddCommGroup (X := T) S 1
  have htop := DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) U hU
  let k := FrameUnitCocycle.frameUnitCech V U CommonLineFrames.CommonLineFrame.left (fun _ => le_rfl)
  let l := FrameUnitCocycle.frameUnitCech V U CommonLineFrames.CommonLineFrame.right (fun _ => le_rfl)
  let m := FrameUnitCocycle.frameUnitCech V U CommonLineFrames.CommonLineFrame.tensor (fun _ => le_rfl)
  have hk := FrameUnitCocycle.frameUnitCech_closed V U CommonLineFrames.CommonLineFrame.left (fun _ => le_rfl)
  have hl := FrameUnitCocycle.frameUnitCech_closed V U CommonLineFrames.CommonLineFrame.right (fun _ => le_rfl)
  have hm := FrameUnitCocycle.frameUnitCech_closed V U CommonLineFrames.CommonLineFrame.tensor (fun _ => le_rfl)
  have he : m = k + l := by
    funext a
    apply Holomorphic.GlobalGluing.holomorphicUnitSection_ext V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
    intro x
    have h0 := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property
    have h1 := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property
    change AnalyticFrameTransitions.framePointTransition V.presentation (a 0).tensor (a 1).tensor x.val h0 h1 =
      AnalyticFrameTransitions.framePointTransition V.presentation (a 0).left (a 1).left x.val h0 h1 *
        AnalyticFrameTransitions.framePointTransition V.presentation (a 0).right (a 1).right x.val h0 h1
    exact CommonLineFrames.commonLineFrame_tensor_transition (a 0) (a 1) x.val h0 h1
  have hsum := Cech.Add.cechAdd_closed (X := T) U S.obj 1 k l hk hl
  have hc := Cech.Add.cechSheafClass_congr (X := T) U S htop 0 m (k + l) hm hsum he
  have ha := Cech.Add.cechSheafClass_add (X := T) U S htop 0 k l hk hl
  have hL := FrameUnitCocycle.nativeHolomorphicLineClass_frameUnits V U L CommonLineFrames.CommonLineFrame.left (fun _ => le_rfl) hU
  have hK := FrameUnitCocycle.nativeHolomorphicLineClass_frameUnits V U K CommonLineFrames.CommonLineFrame.right (fun _ => le_rfl) hU
  have hLK := FrameUnitCocycle.nativeHolomorphicLineClass_frameUnits V U (L.tensor K) CommonLineFrames.CommonLineFrame.tensor (fun _ => le_rfl) hU
  exact hLK.trans (hc.trans (ha.trans (congrArg₂ (· + ·) hL.symm hK.symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTensor
