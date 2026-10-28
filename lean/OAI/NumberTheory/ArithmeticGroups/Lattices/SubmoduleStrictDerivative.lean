import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! # Submodule Strict Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SubmoduleStrictDerivative.Construction

noncomputable section

/-! Strict derivatives of maps into a submodule can be checked after
the isometric inclusion into the ambient normed space. -/

theorem hasStrictFDerivAt_submodule
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Submodule ℝ F) (f : E → P) (f' : E →L[ℝ] P) (a : E)
    (h : HasStrictFDerivAt (fun x => (f x).val) (P.subtypeL.comp f') a) :
    HasStrictFDerivAt f f' a := by
  exact HasStrictFDerivAt.of_comp_of_isEmbedding
    (Topology.IsInducing.subtypeVal.continuousAt_iff.mpr h.continuousAt)
    P.subtypeL.hasStrictFDerivAt Topology.IsEmbedding.subtypeVal h (Filter.Eventually.of_forall (fun _ => rfl))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SubmoduleStrictDerivative.Construction
