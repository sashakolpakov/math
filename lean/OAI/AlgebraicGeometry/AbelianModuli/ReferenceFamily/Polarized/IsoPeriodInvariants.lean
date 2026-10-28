import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactPolarizationPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ComparisonMarkedLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction
import OAI.RepresentationTheory.Theta.Geometric.Rational.CMLinearity
import OAI.RepresentationTheory.Theta.Geometric.Rational.LiftIntertwining

/-! # Iso Period Invariants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.IsoPeriodInvariants

noncomputable section

/-! The native period map of an actual polarized full-level isomorphism
preserves the original rational polarization, integral lattice and Hodge
kernel. This permits transport of arbitrary markings to a test fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps

local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral C.toOver.left := C.variety.property
local instance (C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth C.toOver.hom := C.variety.presentation.smooth

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B)

def levelIsoNativeMap :
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).toOver ⟶
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)).toOver := e.abelian.hom

instance levelIsoNativeMap_group : IsMonHom (levelIsoNativeMap A B e) := by
  let : IsMonHom e.abelian.hom := e.abelianGroup
  exact Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian
    (Projectivity.polarizedNativeProjectivePresentation A) (Projectivity.polarizedNativeProjectivePresentation B) e.abelian.hom

def levelIsoPeriodEquiv :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)) ≃ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)) := by
  let : IsMonHom e.abelian.hom := e.abelianGroup
  exact Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodIso A.abelian B.abelian (Projectivity.polarizedNativeProjectivePresentation A)
    (Projectivity.polarizedNativeProjectivePresentation B) e.abelian

theorem levelIsoPeriodEquiv_polarization
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A))) :
    Intrinsic.ChernPairing.nativePolarizationForm B (levelIsoPeriodEquiv A B e x) (levelIsoPeriodEquiv A B e y) =
      Intrinsic.ChernPairing.nativePolarizationForm A x y := by
  let CA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)
  let CB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)
  let f : CA.toOver ⟶ CB.toOver := e.abelian.hom
  let : IsMonHom e.abelian.hom := e.abelianGroup
  let : IsMonHom f := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian
    (Projectivity.polarizedNativeProjectivePresentation A) (Projectivity.polarizedNativeProjectivePresentation B) e.abelian.hom
  rw [ExactPolarizationPairing.nativePolarizationForm_eq_poincare_exact A, ExactPolarizationPairing.nativePolarizationForm_eq_poincare_exact B]
  change Product.ClassPairingNaturality.nativeProductClassPairing CB CB (Polarization.Adjoints.polarizationBiextensionClass B)
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CB (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x)) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CB (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y)) =
      Product.ClassPairingNaturality.nativeProductClassPairing CA CA (Polarization.Adjoints.polarizationBiextensionClass A)
        (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA x) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA y)
  rw [Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f x, Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f y]
  exact (Product.ClassPairingNaturality.nativeProductClassPairing_pullback CA CA CB CB f f (Polarization.Adjoints.polarizationBiextensionClass B)
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA x) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA y)).symm.trans
      (congrArg (fun c => Product.ClassPairingNaturality.nativeProductClassPairing CA CA c
        (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA x) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA y)) (Polarization.Adjoints.polarizationBiextensionClass_iso A B e))

theorem levelIsoPeriodEquiv_integral
    (x : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A))) :
    levelIsoPeriodEquiv A B e x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)) ↔
      x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)) := by
  let : IsMonHom e.abelian.hom := e.abelianGroup
  let f : (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).toOver ≅
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)).toOver := e.abelian
  let : IsMonHom f.hom := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian
    (Projectivity.polarizedNativeProjectivePresentation A) (Projectivity.polarizedNativeProjectivePresentation B) e.abelian.hom
  exact Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso_integral_iff f x

theorem levelIsoPeriodEquiv_kernel
    (u : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)))) :
    (levelIsoPeriodEquiv A B e).toLinearMap.baseChange ℂ u ∈
      (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B))).ker ↔
        u ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A))).ker := by
  let : IsMonHom e.abelian.hom := e.abelianGroup
  let f : (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).toOver ≅
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)).toOver := e.abelian
  let : IsMonHom f.hom := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian
    (Projectivity.polarizedNativeProjectivePresentation A) (Projectivity.polarizedNativeProjectivePresentation B) e.abelian.hom
  exact RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison.nativeIso_period_kernel_iff f u

theorem levelIsoNativeMap_level (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (levelIsoNativeMap A B e) (ComparisonMarkedLevel.polarizedNativeLevelPoint A c) =
      ComparisonMarkedLevel.polarizedNativeLevelPoint B c := by
  let a := ((A.level.hom.app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))))
    (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase c)).val
  let b := ((B.level.hom.app (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))))
    (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase c)).val
  let p := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (Projectivity.polarizedNativeProjectivePresentation A)
  let q := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B.abelian (Projectivity.polarizedNativeProjectivePresentation B)
  have hf : levelIsoNativeMap A B e = p.hom ≫ e.abelian.hom ≫ q.inv :=
    (Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeComparisonMap_eq A.abelian B.abelian
      (Projectivity.polarizedNativeProjectivePresentation A) (Projectivity.polarizedNativeProjectivePresentation B) e.abelian.hom).symm
  change (a ≫ p.inv) ≫ levelIsoNativeMap A B e = b ≫ q.inv
  rw [hf]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Category.assoc a e.abelian.hom q.inv).symm.trans
    (congrArg (fun h => h ≫ q.inv) (e.level (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase c)))

theorem levelIsoPeriodEquiv_level (c : Multiplicative (Fin (2 * g) → ZMod N)) (r : ℝ)
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)))
    (hv : ComparisonMarkedLevel.polarizedNativeLevelPoint A c =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)).toOver)
        (r • v.val)) :
    ComparisonMarkedLevel.polarizedNativeLevelPoint B c =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)).toOver)
        (r • (levelIsoPeriodEquiv A B e v).val) := by
  rw [← levelIsoNativeMap_level A B e c, hv]
  exact RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential.nativeMap_rational_exp (levelIsoNativeMap A B e) r v

variable {E : Type} [Field E]
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (he : ∀ a, ρ.map a ≫ e.abelian.hom = e.abelian.hom ≫ σ.map a)

include he in
theorem levelIsoPeriodEquiv_action (a : NumberField.RingOfIntegers E)
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A))) :
    levelIsoPeriodEquiv A B e
      (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction A.abelian (Projectivity.polarizedNativeProjectivePresentation A) ρ a v) =
        Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.rationalAction B.abelian (Projectivity.polarizedNativeProjectivePresentation B) σ a
          (levelIsoPeriodEquiv A B e v) := by
  let f := levelIsoNativeMap A B e
  let α := Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap A.abelian (Projectivity.polarizedNativeProjectivePresentation A) ρ a
  let β := Intrinsic.IntegralAction.IntrinsicIntegralAction.nativeMap B.abelian (Projectivity.polarizedNativeProjectivePresentation B) σ a
  have hα : α = ρ.map a := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeComparisonMap_eq A.abelian A.abelian
    (Projectivity.polarizedNativeProjectivePresentation A) (Projectivity.polarizedNativeProjectivePresentation A) (ρ.map a)
  have hβ : β = σ.map a := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeComparisonMap_eq B.abelian B.abelian
    (Projectivity.polarizedNativeProjectivePresentation B) (Projectivity.polarizedNativeProjectivePresentation B) (σ.map a)
  have h : α ≫ f = f ≫ β := by
    rw [hα, hβ]
    exact he a
  change Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift α v) = Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift β (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f v)
  exact RepresentationTheory.Theta.Geometric.Rational.LiftIntertwining.rationalLift_intertwining_apply f α β h v

variable [NumberField E]

def levelIsoFieldEquiv :
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Projectivity.polarizedNativeProjectivePresentation A) ρ
    let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian (Projectivity.polarizedNativeProjectivePresentation B) σ
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)) ≃ₗ[E]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)) := by
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian (Projectivity.polarizedNativeProjectivePresentation B) σ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.abelian (Projectivity.polarizedNativeProjectivePresentation B) σ
  let q := levelIsoPeriodEquiv A B e
  let l := RepresentationTheory.Theta.Geometric.Rational.CMLinearity.rationalMapToCMLinear (E := E) q.toLinearMap (fun a v => by
    change q (Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction A.abelian (Projectivity.polarizedNativeProjectivePresentation A) ρ (a : E) v) =
      Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction B.abelian (Projectivity.polarizedNativeProjectivePresentation B) σ (a : E) (q v)
    rw [Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply, Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldAction_integer_apply]
    exact levelIsoPeriodEquiv_action A B e ρ σ he a v)
  exact LinearEquiv.ofBijective l q.bijective

theorem levelIsoFieldEquiv_apply
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A))) :
    levelIsoFieldEquiv A B e ρ σ he v = levelIsoPeriodEquiv A B e v := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.IsoPeriodInvariants
