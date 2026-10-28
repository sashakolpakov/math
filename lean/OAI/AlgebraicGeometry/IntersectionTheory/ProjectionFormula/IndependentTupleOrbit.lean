import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearTupleMap

/-! # Independent Tuple Orbit -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentTupleOrbit

noncomputable section

/-! Two independent tuples of the same length lie in the same orbit
of the actual linear automorphism group of homogeneous linear forms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_automorphism {n k : ℕ} (L M : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (hM : LinearIndependent ℂ M) :
    ∃ e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1, ∀ a, e (L a) = M a := by
  let b := Module.Basis.span hL
  let c := Module.Basis.span hM
  let f := b.equiv c (Equiv.refl (Fin k))
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e, fun a => ?_⟩
  have hf : f (b a) = c a := Module.Basis.equiv_apply b a c (Equiv.refl _)
  have ha := congrArg (fun x : Submodule.span ℂ (Set.range M) => (x : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)) hf
  rw [he (b a)] at ha
  simpa only [b, c, Module.Basis.coe_span_apply] using ha

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentTupleOrbit
