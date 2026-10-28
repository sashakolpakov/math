import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Data
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm

/-! # Frames -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Frames

noncomputable section

/-! Smooth form coordinates in the original holomorphic frames. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {U : Opens M} (i : M)
  (hU : U ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (n : ℕ)

def holomorphicLineSmoothFormOfFrame (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n :=
  ⟨fun j => SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen
      (HolomorphicSection.Data.holomorphicOpenRestriction (inf_le_inf_right (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j) hU)
        (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val))
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left a), by
    intro j k x hx hj hk
    simp only [SmoothScalarForm.smoothScalarOpenFormMul_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply]
    change (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i k).val ⟨x, hU hx, hk⟩ • a ⟨x, hx⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u j k).val ⟨x, hj, hk⟩ •
        ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hU hx, hj⟩ • a ⟨x, hx⟩)
    rw [← Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_cocycle E M u i j k x (hU hx) hj hk,
      smul_smul, mul_comm]⟩

theorem holomorphicLineSmoothFormOfFrame_apply (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (j : M) (x : ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j)) :
    (holomorphicLineSmoothFormOfFrame u i hU n a).val j x =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hU x.property.1, x.property.2⟩ •
        a ⟨x, x.property.1⟩ := by
  exact SmoothScalarForm.smoothScalarOpenFormMul_apply _ _ x

def holomorphicLineSmoothFrameValue (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (le_inf le_rfl hU) (a.val i)

theorem holomorphicLineSmoothFrameValue_ofFrame (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    holomorphicLineSmoothFrameValue u i hU n (holomorphicLineSmoothFormOfFrame u i hU n a) = a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [holomorphicLineSmoothFrameValue, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply,
    holomorphicLineSmoothFormOfFrame_apply,
    Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition_self E M u i x.val (hU x.property), one_smul]

theorem holomorphicLineSmoothFormOfFrame_frameValue (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) :
    holomorphicLineSmoothFormOfFrame u i hU n (holomorphicLineSmoothFrameValue u i hU n a) = a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro j x
  rw [holomorphicLineSmoothFormOfFrame_apply]
  exact (a.property i j x.val x.property.1 (hU x.property.1) x.property.2).symm

def holomorphicLineSmoothFrameEquiv :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n where
  toFun := holomorphicLineSmoothFrameValue u i hU n
  invFun := holomorphicLineSmoothFormOfFrame u i hU n
  left_inv := holomorphicLineSmoothFormOfFrame_frameValue u i hU n
  right_inv := holomorphicLineSmoothFrameValue_ofFrame u i hU n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Frames
