import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CountableImages
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestFiberIso

/-! # Fine PEL Countable Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Original reference points occurring in a smooth integral subspace
of the actual fine PEL scheme have a countable holomorphic image cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)] (f : S ⟶ M.complexFiber κ)

include hM hκ f in
theorem Models.FinePELModel.exists_countable_reference_images :
    let V := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set V) (period : I → V → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ a : P.domain, (∃ y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, y ≫ f = M.referencePoint hM κ hP hκ a) →
        ∃ i, a.val ∈ period i '' O i := by
  let A := M.complexTestFamily κ f
  obtain ⟨I, hI, O, period, hO, hcover⟩ :=
    Family.CountableImages.exists_countable_native_reference_images A.polarized A.action P hP (Nat.pos_of_ne_zero (NeZero.ne N))
  refine ⟨I, hI, O, period, hO, ?_⟩
  intro a ha
  obtain ⟨y, hy⟩ := ha
  exact hcover a (Reference.Fiber.referenceAnalyticFiber P hP a)
    (Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP)
    ⟨y, M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy,
      M.nativeReferenceTestFiberIso_group hM κ hP hκ f a y hy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
