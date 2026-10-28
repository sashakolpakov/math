import OAI.RepresentationTheory.Theta.Geometric.Reference.IsoLabels
import OAI.RepresentationTheory.Theta.Geometric.CountableKernelCharts

/-! # Countable Reference Iso Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Countably many holomorphic charts account for all reference ball
points whose abelian fibers occur in one actual compatible family chart. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport A ρ F)
    {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.exists_countable_reference_iso_charts :
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set (Intrinsic.FamilyFrames.FamilyChartBase C))
      (period : I → Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ O i ⊆ H.compatible.neighborhood ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ (y : P.domain) (R : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P y) (M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel R hP)
        (z : H.compatible.neighborhood)
        (e : M.abelian.toOver ≅ (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver),
        IsMonHom e.hom → ∃ i, z.val ∈ O i ∧ period i z.val = y.val := by
  have hex (t : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C)) :=
    CountableKernelCharts.exists_countable_kernel_coordinate_charts (H.referenceMarkedMatrix P hP t)
      H.compatible.neighborhood H.compatible.isOpen (H.referenceMarkedMatrix_holomorphic P hP t)
  choose I hI O period hO hcover using hex
  let (t : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C)) : Countable (I t) := hI t
  let J := Σ t : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C), I t
  refine ⟨J, inferInstance, fun i => O i.1 i.2, fun i => period i.1 i.2,
    fun i => hO i.1 i.2, ?_⟩
  intro y R M z e he
  let : IsMonHom e.hom := he
  let t := H.referenceIsoLabel M z e
  obtain ⟨i, hzi, hip⟩ := hcover t z.val z.property y.val (H.referenceIsoLabel_kernel M z e)
  exact ⟨⟨t, i⟩, hzi, hip⟩

end

end OAI.RepresentationTheory.Theta.Geometric
