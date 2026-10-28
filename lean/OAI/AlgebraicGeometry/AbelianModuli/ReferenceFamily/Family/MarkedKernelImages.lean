import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CentralPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CountableTransportCover
import OAI.RepresentationTheory.Theta.Geometric.CountableKernelCharts
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison
import OAI.RepresentationTheory.Theta.Geometric.BaseChangeCancellation
import OAI.RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates
import Mathlib.LinearAlgebra.Countable

/-! # Marked Kernel Images -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Countably many holomorphic images detect any collection of actual
abelian fibers with a fixed rational marking space and a specified line
in their native Hodge kernels. The rational Hermitian form need not be the
reference form, and no continuity of the collection is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation Family.MarkingCoordinates.markingComplexBasis

variable {E : Type} [Field E] [NumberField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

section

variable (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F)

abbrev Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel := NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ]
  Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).variety

instance Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.rationalKernelLabel_countable : Countable (Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel (E := E) (A := A) (C := C)) :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

variable (j : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (t : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel (E := E) (A := A) (C := C))

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedKernelCoefficients : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin F.rank → ℂ) :=
  ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun.toLinearMap.comp
    ((t.baseChange ℂ).comp j)).toContinuousLinearMap

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedKernelMatrix (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin H.dimension → ℂ) :=
  (H.matrix z).comp (H.markedKernelCoefficients j t)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedKernelMatrix_holomorphic :
    DifferentiableOn ℂ (H.markedKernelMatrix j t) H.compatible.neighborhood :=
  H.holomorphic.clm_comp (differentiableOn_const (H.markedKernelCoefficients j t))

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedKernelMatrix_kernel_iff (z : H.compatible.neighborhood) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    H.markedKernelMatrix j t z v = 0 ↔
      (H.rationalTransport z).toLinearMap.baseChange ℂ
        (t.baseChange ℂ (j v)) ∈
          (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety).ker := by
  change H.matrix z ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun (t.baseChange ℂ (j v))) = 0 ↔ _
  rw [H.matrix_kernel_iff]

variable {B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (m : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (z : H.compatible.neighborhood)
    (e : B.toOver ≅ (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver)
    [IsMonHom e.hom]

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedIsoLabel : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel (E := E) (A := A) (C := C) :=
  (H.rationalTransport z).symm.toLinearMap.comp ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).comp m)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedIsoLabel_complex (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    (H.rationalTransport z).toLinearMap.baseChange ℂ
      ((H.markedIsoLabel m z e).baseChange ℂ u) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).baseChange ℂ (m.baseChange ℂ u) := by
  exact (RepresentationTheory.Theta.Geometric.BaseChangeCancellation.baseChange_equiv_cancel (H.rationalTransport z)
    ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).comp m) u).trans
      (LinearMap.congr_fun (LinearMap.baseChange_comp m (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom)) u)

attribute [local irreducible] Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedKernelMatrix Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedKernelCoefficients

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.markedIsoLabel_kernel (a : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hk : ∀ v, m.baseChange ℂ (j v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B).ker ↔
      v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a}) :
    (H.markedKernelMatrix j (H.markedIsoLabel m z e) z).ker =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a} := by
  ext v
  change H.markedKernelMatrix j (H.markedIsoLabel m z e) z v = 0 ↔ _
  rw [H.markedKernelMatrix_kernel_iff, H.markedIsoLabel_complex]
  exact (RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison.nativeIso_period_kernel_iff e (m.baseChange ℂ (j v))).trans (hk v)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.exists_countable_marked_kernel_charts :
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C))
      (period : I → RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ O i ⊆ H.compatible.neighborhood ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ (a : Geometry.ComplexBall.PrescribedSignsB.BallChart) (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (m : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B),
        (∀ v, m.baseChange ℂ (j v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B).ker ↔
          v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a}) →
        ∀ (z : H.compatible.neighborhood)
          (e : B.toOver ≅ (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver),
          IsMonHom e.hom → ∃ i, z.val ∈ O i ∧ period i z.val = a := by
  have hex (t : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel (E := E) (A := A) (C := C)) :=
    RepresentationTheory.Theta.Geometric.CountableKernelCharts.exists_countable_kernel_coordinate_charts (H.markedKernelMatrix j t)
      H.compatible.neighborhood H.compatible.isOpen (H.markedKernelMatrix_holomorphic j t)
  choose I hI O period hO hcover using hex
  let (t : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel (E := E) (A := A) (C := C)) : Countable (I t) := hI t
  let J := Σ t : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalKernelLabel (E := E) (A := A) (C := C), I t
  refine ⟨J, inferInstance, fun i => O i.1 i.2, fun i => period i.1 i.2,
    fun i => hO i.1 i.2, ?_⟩
  intro a B m hk z e he
  let : IsMonHom e.hom := he
  let t := H.markedIsoLabel m z e
  obtain ⟨i, hzi, hip⟩ := hcover t z.val z.property a (H.markedIsoLabel_kernel j m z e a hk)
  exact ⟨⟨t, i⟩, hzi, hip⟩

end

variable [IsIntegral S.left] [Smooth S.hom] [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)]

theorem Family.MarkedKernelImages.exists_countable_native_marked_kernel_images
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (j : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hN : 0 < N) :
    let V := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ
    ∃ I : Type, Countable I ∧ ∃ (O : I → Set V) (period : I → V → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      (∀ i, IsOpen (O i) ∧ DifferentiableOn ℂ (period i) (O i)) ∧
      ∀ (a : Geometry.ComplexBall.PrescribedSignsB.BallChart) (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (m : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B),
        (∀ v, m.baseChange ℂ (j v) ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B).ker ↔
          v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a}) →
        (∃ (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
          (e : B.toOver ≅ (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A y).variety.toOver), IsMonHom e.hom) →
        ∃ i, a ∈ period i '' O i := by
  obtain ⟨T, hT, x, C, F, H, hcover⟩ := Family.CountableTransportCover.exists_countable_native_transport_cover A ρ hN
  have : Countable T := hT
  have hex (c : T) := (H c).exists_countable_marked_kernel_charts j
  choose I hI O period hO hmatch using hex
  have (c : T) : Countable (I c) := hI c
  let e (c : T) := RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates.fixedFamilyBaseCoordinates (C c)
  let J := Σ c : T, I c
  refine ⟨J, inferInstance, fun i => e i.1 ⁻¹' O i.1 i.2, fun i v => period i.1 i.2 (e i.1 v), ?_, ?_⟩
  · intro i
    exact ⟨(hO i.1 i.2).1.preimage (e i.1).continuous,
      (hO i.1 i.2).2.2.comp (e i.1).differentiable.differentiableOn (fun _ hv => hv)⟩
  · intro a B m hk ha
    obtain ⟨y, iso, hiso⟩ := ha
    obtain ⟨c, z, hz⟩ := hcover y
    subst y
    obtain ⟨i, hzi, hip⟩ := hmatch c a B m hk z iso hiso
    refine ⟨⟨c, i⟩, (e c).symm z.val, ?_, ?_⟩
    · change e c ((e c).symm z.val) ∈ O c i
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hzi
    · change period c i (e c ((e c).symm z.val)) = a
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact hip

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
