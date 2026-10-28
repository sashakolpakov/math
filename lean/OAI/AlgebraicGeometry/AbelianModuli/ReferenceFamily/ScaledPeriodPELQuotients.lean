import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedPELQuotients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ComparisonMarkedLevel

/-! # Scaled Period PEL Quotients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledPeriodPELQuotients

noncomputable section

/-! A cleared isometry between the actual rational period spaces gives
a paired PEL quotient. Arbitrary field markings can supply this isometry;
the ordered-level condition is checked through the native exponential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation

local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral C.toOver.left := C.variety.property
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth C.toOver.hom := C.variety.presentation.smooth

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [CharZero K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {t : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)} (A B : PEL.Objects.PELObject P iota N (Over.mk t))

local notation "PA" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
local notation "PB" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian PA
local notation "B₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.polarized.abelian PB

omit [NeZero N] in
theorem exists_paired_quotient_of_scaled_period_isometry
    (e : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ ≃ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B₀)
    (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A₀) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀) e.toLinearMap)
    (hp : ∀ x y, Intrinsic.ChernPairing.nativePolarizationForm B.polarized (e x) (e y) =
      Intrinsic.ChernPairing.nativePolarizationForm A.polarized x y)
    (ha : ∀ a, e.toLinearMap.comp (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A.polarized.abelian PA A.action a)) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B.polarized.abelian PB B.action a)).comp e.toLinearMap)
    (D : ℕ) (hD : 0 < D) (hmod : Nat.ModEq N (D ^ 2) 1)
    (hΛ : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A₀, D • e x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods B₀)
    (hΛ' : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods B₀, D • e.symm x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A₀)
    {I : Type*} (label : I → Multiplicative (Fin (2 * (3 * s)) → ZMod N))
    (hlabel : Function.Surjective label) (v : I → Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀)
    (hA : ∀ i, Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint A.polarized (label i) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A₀).toOver) ((N : ℝ)⁻¹ • (v i).val))
    (hB : ∀ i, Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint B.polarized (label i) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (B₀).toOver) ((N : ℝ)⁻¹ • (D • e (v i)).val)) :
    ∃ q : Paired.PELQuotients.PairedPELQuotient A B (D ^ 2),
      CrossPoincarePeriodMaps.polarizedAbelianPeriodMap A.polarized B.polarized q.forward.isogeny.hom = D • e.toLinearMap ∧
      CrossPoincarePeriodMaps.polarizedAbelianPeriodMap B.polarized A.polarized q.reverse.isogeny.hom = D • e.symm.toLinearMap := by
  let : IsLocallyNoetherian (Over.mk t).left := inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)
  let q := D • e.toLinearMap
  let r := D • e.symm.toLinearMap
  have hq : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A₀) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀) q :=
    ScaledMarkedPeriodTransport.isHodgeMap_nsmul he D
  have hr : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B₀) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A₀) r :=
    ScaledMarkedPeriodTransport.isHodgeMap_nsmul (HodgeInverse.isHodgeMap_inverse _ _ e he) D
  have hqr : r.comp q = D ^ 2 • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A₀ →ₗ[ℚ] _) := by
    apply LinearMap.ext
    intro x
    change D • e.symm (D • e x) = D ^ 2 • x
    rw [map_nsmul, e.symm_apply_apply, smul_smul, pow_two]
  have hrq : q.comp r = D ^ 2 • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B₀ →ₗ[ℚ] _) := by
    apply LinearMap.ext
    intro x
    change D • e (D • e.symm x) = D ^ 2 • x
    rw [map_nsmul, e.apply_symm_apply, smul_smul, pow_two]
  let f := Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeIsogeny A.polarized.abelian B.polarized.abelian PA PB
    q hq hΛ r hr hΛ' (D ^ 2) (pow_pos hD 2) hqr hrq
  let f' := Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeIsogeny B.polarized.abelian A.polarized.abelian PB PA
    r hr hΛ' q hq hΛ (D ^ 2) (pow_pos hD 2) hrq hqr
  have hfe : Etale f.hom.left :=
    (Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_finite_etale A.polarized.abelian B.polarized.abelian PA PB
      q hq hΛ r hr hΛ' (D ^ 2) (pow_pos hD 2) hqr hrq).2.1
  have hff' : f.hom ≫ f'.hom = (𝟙 A.polarized.abelian.scheme) ^ (D ^ 2) :=
    Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMaps_scalar_composition A.polarized.abelian B.polarized.abelian PA PB
      q hq hΛ r hr hΛ' (D ^ 2) hqr
  have hf'f : f'.hom ≫ f.hom = (𝟙 B.polarized.abelian.scheme) ^ (D ^ 2) :=
    Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMaps_scalar_composition B.polarized.abelian A.polarized.abelian PB PA
      r hr hΛ' q hq hΛ (D ^ 2) hrq
  have hf : CrossPoincarePeriodMaps.polarizedAbelianPeriodMap A.polarized B.polarized f.hom = q :=
    ScaledMarkedIsogenies.AbelianNativeAdapter.originalIntegralHodgeMap_originalPeriodMap A.polarized.abelian B.polarized.abelian PA PB q hq hΛ
  have hf' : CrossPoincarePeriodMaps.polarizedAbelianPeriodMap B.polarized A.polarized f'.hom = r :=
    ScaledMarkedIsogenies.AbelianNativeAdapter.originalIntegralHodgeMap_originalPeriodMap B.polarized.abelian A.polarized.abelian PB PA r hr hΛ'
  have hpol : AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom A.polarized.dual B.polarized.dual
      B.polarized.polarization = A.polarized.polarization.isogeny.hom ^ (D ^ 2) := by
    apply Polarization.PeriodSimilitude.polarization_pullback_of_period_similitude A.polarized B.polarized f.hom (D ^ 2)
    intro x y
    rw [hf]
    change Intrinsic.ChernPairing.nativePolarizationForm B.polarized (D • e x) (D • e y) =
      D ^ 2 • Intrinsic.ChernPairing.nativePolarizationForm A.polarized x y
    simp only [map_nsmul, LinearMap.smul_apply]
    rw [hp, smul_smul, pow_two]
  have hact (a : NumberField.RingOfIntegers E) :
      A.action.map a ≫ f.hom = f.hom ≫ B.action.map a := by
    apply Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_intertwines A.polarized.abelian B.polarized.abelian PA PB
      q hq hΛ A.action B.action
    intro b
    simpa only [q, LinearMap.smul_comp, LinearMap.comp_smul] using
      congrArg (fun l => D • l) (ha b)
  have hlevel (T : Over Foundations.Scheme.ProjectiveSpace.complexBase)
      (c : LocallyConstant T.left (Frame.Labels.LevelCover.Coefficients (3 * s) N)) :
      (A.polarized.level.hom.app (.op T) c).val ≫ f.hom =
        (B.polarized.level.hom.app (.op T) c).val := by
    apply RepresentationTheory.Theta.Geometric.PresentedLevelComparison.original_level_comparison_of_presented_points
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation A.polarized) (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation B.polarized)
      A.polarized.level B.polarized.level f.hom ?_ T c
    intro a
    obtain ⟨i, rfl⟩ := hlabel a
    let f₀ := (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.polarized.abelian PA).hom ≫ f.hom ≫
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B.polarized.abelian PB).inv
    have hf₀ : Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f₀ = q :=
      Reference.IntegralHodgeMaps.AbelianIntrinsicAdapter.originalIntegralHodgeMap_rational A.polarized.abelian B.polarized.abelian PA PB q hq hΛ
    exact RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential.nativeMap_point_of_rational_exp f₀ (N : ℝ)⁻¹ (v i) (D • e (v i))
      (Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint A.polarized (label i))
      (Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint B.polarized (label i)) (hA i) (hB i)
      (LinearMap.congr_fun hf₀ (v i))
  let fPEL : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient A B (D ^ 2) := {
    isogeny := f
    etale := hfe
    polarization := hpol
    action := fun a => (hact a).symm
    marking := hlevel }
  exact ⟨{
    forward := fPEL
    reverse := Paired.PELQuotients.scalarComplementPELQuotient fPEL f' (pow_pos hD 2) hmod hff' hf'f
    forward_reverse := hff'
    reverse_forward := hf'f }, hf, hf'⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledPeriodPELQuotients
