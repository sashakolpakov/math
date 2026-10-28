import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.ActionTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.HermitianTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse

/-! # Scaled Marked Period Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedPeriodTransport

noncomputable section

/-! Scaling the actual marked rational period transport by the integer
that clears a lattice map preserves Hodge type and integral action. The
opposite scaled transport has exactly the square scalar as complement.
The polarization multiplier is the same square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem isHodgeMap_nsmul
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} {K : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V}
    {f : U →ₗ[ℚ] V} (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap H K f) (D : ℕ) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap H K (D • f) := by
  intro x hx
  have hb := congrArg (fun m => m x)
    (map_nsmul (LinearMap.baseChangeHom ℚ ℂ U V) D f)
  change (D • f).baseChange ℂ x = D • f.baseChange ℂ x at hb
  rw [hb]
  exact nsmul_mem (hf x hx) D

namespace NativePELMarking

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (PA : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (PB : Foundations.Scheme.SmoothProjective.ProjectivePresentation B.scheme.left B.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

theorem markedPeriodTransport_inverse_apply (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B A PB PA σ ρ s hs hg hdegree u.symm
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u x) = x := by
  apply (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A PA ρ s hs hg hdegree).injective
  rw [Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates, Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates]
  exact u.symm_apply_apply _

theorem markedPeriodTransport_reverse :
    Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B A PB PA σ ρ s hs hg hdegree u.symm =
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).symm := by
  apply LinearEquiv.ext
  intro x
  apply (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).injective
  have h := markedPeriodTransport_inverse_apply B A PB PA σ ρ s hs hg hdegree u.symm x
  simpa only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply] using h

theorem markedPeriodTransport_reverse_isHodgeMap
    (hu : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA))
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B A PB PA σ ρ s hs hg hdegree u.symm).toLinearMap := by
  rw [markedPeriodTransport_reverse]
  exact HodgeInverse.isHodgeMap_inverse _ _ _ hu

def scaledMarkedCoordinateIso (D : ℕ) (hD : 0 < D) : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  u.trans (LinearEquiv.smulOfNeZero E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (D : E)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)))

omit [Algebra ℚ E] in
theorem scaledMarkedCoordinateIso_apply (D : ℕ) (hD : 0 < D) (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    scaledMarkedCoordinateIso u D hD x = D • u x := by
  change (D : E) • u x = D • u x
  exact Nat.cast_smul_eq_nsmul E D (u x)

theorem scaledMarkedCoordinateIso_periods (D : ℕ) (hD : 0 < D) :
    (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree
      (scaledMarkedCoordinateIso u D hD)).toLinearMap =
        D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree).injective
  change Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree (scaledMarkedCoordinateIso u D hD) x) =
    Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree
      (D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u x)
  rw [Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates, scaledMarkedCoordinateIso_apply, map_nsmul,
    Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates]

theorem scaledMarkedPeriodTransport_comp (D : ℕ) :
    (D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B A PB PA σ ρ s hs hg hdegree u.symm).toLinearMap).comp
        (D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap) =
      D ^ 2 • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA) →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) := by
  apply LinearMap.ext
  intro x
  change D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B A PB PA σ ρ s hs hg hdegree u.symm
      (D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u x) = D ^ 2 • x
  rw [map_nsmul, markedPeriodTransport_inverse_apply, smul_smul, pow_two]

theorem scaledMarkedPeriodTransport_integral (D : ℕ)
    (m : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A PA ρ s hs hg hdegree →ₗ[ℤ] Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B PB σ s hs hg hdegree)
    (hm : ∀ x, (m x).val = D • u x.val)
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) (hx : x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A PA)) :
    (D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap) x ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B PB) := by
  apply (Marked.PeriodTransport.IntrinsicPELMarking.coordinates_mem_markedLattice B PB σ s hs hg hdegree _).mp
  change Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B PB σ s hs hg hdegree
    (D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u x) ∈ _
  rw [map_nsmul, Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates]
  let a : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A PA ρ s hs hg hdegree :=
    ⟨Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A PA ρ s hs hg hdegree x,
      (Marked.PeriodTransport.IntrinsicPELMarking.coordinates_mem_markedLattice A PA ρ s hs hg hdegree x).mpr hx⟩
  exact hm a ▸ (m a).property

theorem scaledMarkedPeriodTransport_integral_action (D : ℕ)
    (a : NumberField.RingOfIntegers E) :
    (D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap).comp
        (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A PA ρ a)) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B PB σ a)).comp
        (D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u).toLinearMap) := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (Marked.ActionTransport.IntrinsicPELMarking.markedPeriodTransport_integral_action A B PA PB ρ σ s hs hg hdegree u a) x
  change D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A PA ρ a) x) =
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B PB σ a)
      (D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A B PA PB ρ σ s hs hg hdegree u x)
  rw [map_nsmul]
  exact congrArg (fun y => D • y) h

end NativePELMarking

namespace NativeHermitianMarking

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.ActionTransport.IntrinsicPELMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : ActionData.RosatiConjugation A ρ) (hσ : ActionData.RosatiConjugation B σ)
    (ξ : E) (hξ : ξ ≠ 0) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

include hξ in
theorem scaledMarkedPeriodTransport_polarization
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B σ s hs hg hdegree hσ ξ) (u x) (u y) =
        Datum.RankThreePELDatum.matrixHermitian (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y)
    (D : ℕ)
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    Intrinsic.ChernPairing.nativePolarizationForm B
      (D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
        (Polarized.Projectivity.polarizedNativeProjectivePresentation B) ρ σ s hs hg hdegree u x)
      (D • Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
        (Polarized.Projectivity.polarizedNativeProjectivePresentation B) ρ σ s hs hg hdegree u y) =
      D ^ 2 • Intrinsic.ChernPairing.nativePolarizationForm A x y := by
  rw [map_nsmul, map_nsmul, LinearMap.smul_apply,
    Marked.HermitianTransport.IntrinsicHermitianMarking.markedHermitian_isometry_preserves_polarization A B ρ σ s hs hg hdegree hρ hσ ξ hξ u hu,
    smul_smul, pow_two]

end NativeHermitianMarking

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedPeriodTransport
