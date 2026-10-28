import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CountableTransportCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.ChartCover
import OAI.RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates

/-! # Countable Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CountableImages

noncomputable section

/-! All reference fibers occurring in a smooth integral family are
covered by countably many holomorphic images from its intrinsic dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)] {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include ρ in
theorem exists_countable_native_reference_images (hN : 0 < N) :
    let V := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set V) (period : I → V → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ (a : P.domain) (R : Reference.Fiber.ReferenceAnalyticFiber P a) (M : Reference.AlgebraicModel.ReferenceAlgebraicModel R hP),
        (∃ (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
          (e : M.abelian.toOver ≅ (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety.toOver), IsMonHom e.hom) →
        ∃ i, a.val ∈ period i '' O i := by
  obtain ⟨T, hT, x, C, F, H, hcover⟩ := CountableTransportCover.exists_countable_native_transport_cover A ρ hN
  have : Countable T := hT
  have hex (c : T) := (H c).exists_countable_reference_iso_charts P hP
  choose I hI O period hO hmatch using hex
  have (c : T) : Countable (I c) := hI c
  let e (c : T) := RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates.fixedFamilyBaseCoordinates (C c)
  let J := Σ c : T, I c
  refine ⟨J, inferInstance, fun i => e i.1 ⁻¹' O i.1 i.2, fun i v => period i.1 i.2 (e i.1 v), ?_, ?_⟩
  · intro i
    exact ⟨(hO i.1 i.2).1.preimage (e i.1).continuous,
      (hO i.1 i.2).2.2.comp (e i.1).differentiable.differentiableOn (fun _ hv => hv)⟩
  · intro a R M ha
    obtain ⟨y, iso, hiso⟩ := ha
    obtain ⟨c, z, hz⟩ := hcover y
    subst y
    obtain ⟨i, hzi, hip⟩ := hmatch c a R M z iso hiso
    refine ⟨⟨c, i⟩, (e c).symm z.val, ?_, ?_⟩
    · change e c ((e c).symm z.val) ∈ O c i
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hzi
    · change period c i (e c ((e c).symm z.val)) = a.val
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hip

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CountableImages
