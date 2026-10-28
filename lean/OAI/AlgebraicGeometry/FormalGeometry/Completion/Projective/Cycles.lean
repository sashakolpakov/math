import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.FiniteModelCompletion
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectivePerfectCech

/-! # Cycles -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Cycles.Construction

noncomputable section

/-! Formal zero-cycle surjectivity for the actual projective Cech complex.
The finite cochain model is constructed from projective geometry and flatness. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]

/-- Every compatible reduced zero-cycle in the actual projective Cech complex
comes from its completed kernel. The finite model is proved, not supplied. -/
theorem projectiveCech_reducedKernelComparison_surjective
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (I : Ideal Γ(Spec (.of Γ(S, ⊤)), ⊤)) :
    Finite.FiniteModelCompletion.Construction.FormalZeroCycleComparisonSurjective I
      (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.complex X P L.sheaf) := by
  let e : Γ(Spec (.of Γ(S, ⊤)), ⊤) ≃+* Γ(S, ⊤) :=
    (Scheme.ΓSpecIso (.of Γ(S, ⊤))).commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(Spec (.of Γ(S, ⊤)), ⊤) :=
    isNoetherianRing_of_ringEquiv Γ(S, ⊤) e.symm
  obtain ⟨D, φ, _hq, _hb, hfinite, _hp, htensor⟩ :=
    Quotients.FiniteDescent.ProjectivePerfectCech.Construction.ProjectiveCechComplex.exists_finite_projective X P L
  have := hfinite 0
  have := hfinite 1
  exact Finite.FiniteModelCompletion.Construction.formalZeroCycleComparisonSurjective_of_tensor_finite_model I φ
    (fun n => htensor (_ ⧸ I ^ n))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Cycles.Construction
