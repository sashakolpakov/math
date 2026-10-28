import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge

/-! # One Form Wedge Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormWedgeEvaluation

noncomputable section

/-! The original factorial-normalized exterior product of two one-forms has the usual explicit alternating value. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem covectorWedge_one_one_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E [⋀^Fin 1]→L[ℝ] ℂ) (v : Fin 2 → E) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b v = a (fun _ => v 0) * b (fun _ => v 1) - a (fun _ => v 1) * b (fun _ => v 0) := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_apply, hu]
  rw [Finset.sum_pair (by decide : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1)]
  simp [Fin.fin_one_eq_zero, sub_eq_add_neg]

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {U : Opens M}

local instance oneWedge_tangentNormedGroup (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance oneWedge_tangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

theorem openManifoldWedge_one_one_apply (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (x : U) (v : Fin 2 → TangentSpace 𝓘(ℝ, E) x.val) :
    Open.ManifoldWedge.openManifoldWedge a b x v = a x (fun _ => v 0) * b x (fun _ => v 1) -
      a x (fun _ => v 1) * b x (fun _ => v 0) := by
  rw [Open.ManifoldWedge.openManifoldWedge_apply, covectorWedge_one_one_apply]

theorem openManifoldWedge_one_one_self (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) : Open.ManifoldWedge.openManifoldWedge a a = 0 := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [openManifoldWedge_one_one_apply]
  change a x (fun _ => v 0) * a x (fun _ => v 1) - a x (fun _ => v 1) * a x (fun _ => v 0) = 0
  ring

theorem openManifoldWedge_one_one_antisymm (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Open.ManifoldWedge.openManifoldWedge a b = -Open.ManifoldWedge.openManifoldWedge b a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change Open.ManifoldWedge.openManifoldWedge a b x v = -Open.ManifoldWedge.openManifoldWedge b a x v
  rw [openManifoldWedge_one_one_apply, openManifoldWedge_one_one_apply]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormWedgeEvaluation
