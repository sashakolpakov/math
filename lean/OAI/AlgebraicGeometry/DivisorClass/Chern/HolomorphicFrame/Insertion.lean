import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Frames
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneFormProjection

/-! # Insertion -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Insertion

noncomputable section

/-! A compact scalar form in an original holomorphic frame gives a genuine global bundle form through the original transition functions. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (i : M) (n : ℕ)
  (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i : Set M))

def holomorphicLineSmoothFrameInsertion :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n :=
  (Holomorphic.SupportedForms.holomorphicLineSupportedExtension u (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n f hf hs).comp
    ((HolomorphicSmooth.Frames.holomorphicLineSmoothFrameEquiv u i le_rfl n).symm.toLinearMap.comp
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)))

theorem holomorphicLineSmoothFrameInsertion_apply (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (j : M) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j))
    (hx : (x : M) ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    (holomorphicLineSmoothFrameInsertion u i n f hf hs a).val j x =
      f x • ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hx, x.property.2⟩ • a x.val) := by
  change (Holomorphic.SupportedForms.holomorphicLineSupportedExtension u (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n f hf hs
    (HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame u i le_rfl n (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen _ a))).val j x = _
  rw [Holomorphic.SupportedForms.holomorphicLineSupportedExtension_apply_mem u _ n f hf hs _ j x hx,
    HolomorphicSmooth.Frames.holomorphicLineSmoothFormOfFrame_apply, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_apply]

theorem holomorphicLineSmoothFrameInsertion_in_frame (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)) :
    (holomorphicLineSmoothFrameInsertion u i n f hf hs a).val i x = f x • a x.val := by
  rw [holomorphicLineSmoothFrameInsertion_apply u i n f hf hs a i x x.property.2,
    Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_self E M u i x.val x.property.2, one_smul]

theorem holomorphicLineSmoothFrameInsertion_zero (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (j : M) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) (hx : (x : M) ∉ tsupport f) :
    (holomorphicLineSmoothFrameInsertion u i n f hf hs a).val j x = 0 :=
  Holomorphic.SupportedForms.holomorphicLineSupportedExtension_apply_zero u _ n f hf hs _ j x hx

theorem holomorphicLineSmoothFrameInsertion_zero_of_scalar_zero (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (j : M) (x : ↥(⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) (ha : a x.val = 0) :
    (holomorphicLineSmoothFrameInsertion u i n f hf hs a).val j x = 0 := by
  by_cases hx : (x : M) ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i
  · rw [holomorphicLineSmoothFrameInsertion_apply u i n f hf hs a j x hx, ha]
    let T := TangentSpace 𝓘(ℝ, E) x.val [⋀^Fin n]→L[ℝ] ℂ
    let t := (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hx, x.property.2⟩
    exact (congrArg (fun b : T => f x • b) (smul_zero (A := T) t)).trans (smul_zero (A := T) (f x))
  · exact holomorphicLineSmoothFrameInsertion_zero u i n f hf hs a j x (fun ht => hx (hs ht))

def holomorphicLineAntiFrameInsertion :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 :=
  (Holomorphic.OneFormProjection.holomorphicLineOneAntiProjection u ⊤).comp (holomorphicLineSmoothFrameInsertion u i 1 f hf hs)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Insertion
