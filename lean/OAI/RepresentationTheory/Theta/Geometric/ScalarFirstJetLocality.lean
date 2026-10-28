import OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJet
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! # Scalar First Jet Locality -/

namespace OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJetLocality

noncomputable section

/-! The actual scalar first jet depends only on the local germ. -/

open scoped _root_.Topology

theorem scalarFirstJet_congr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (z a : V) (h : f =ᶠ[𝓝 z] g) :
    ScalarFirstJet.scalarFirstJet f z a = ScalarFirstJet.scalarFirstJet g z a := by
  apply TrivSqZeroExt.ext
  · exact h.eq_of_nhds
  · exact congrArg (fun d : V →L[ℂ] ℂ => d a) h.fderiv_eq

end

end OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJetLocality
