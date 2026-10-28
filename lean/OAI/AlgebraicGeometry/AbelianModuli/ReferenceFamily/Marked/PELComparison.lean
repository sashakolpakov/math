import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexUniversal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ComparisonMarkedLevel
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparisonAction

/-! # PEL Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PELComparison

noncomputable section

/-! Arbitrary full field markings recover the actual PEL fiber from
its active Hodge kernel, integral lattice, polarization and ordered level.
The markings need not identify their Hermitian form with the reference form. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
  RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedNativePresentation
attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm Intrinsic.ChernPairing.nativePolarizationForm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ) (hP : P.IsAdmissible)
    {S T : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (A : PEL.Objects.PELObject P iota N (Complex.BallPeriods.restrictComplexBase κ S))
    (B : PEL.Objects.PELObject P iota N (Complex.BallPeriods.restrictComplexBase κ T))
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T)
    (mA : let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action x
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized x).variety)
    (mB : let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule B.polarized B.action y
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation B.polarized y).variety)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hi : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
      mA v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized x).variety ↔
        mB v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation B.polarized y).variety)
    (hp : ∀ v w,
      RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm B.polarized y (mB v) (mB w) =
        RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm A.polarized x (mA v) (mA w))
    (hk : (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection A.polarized A.action x s mA P hP).ker =
      (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection B.polarized B.action y s mB P hP).ker)

omit [IsGalois ℚ E] in
theorem fieldMarkingFirstProjection_kernel_eq_of_normalized
    (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (heq : ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection A.polarized A.action x s mA P hP).comp e₀.toLinearMap).ker =
      ((RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection B.polarized B.action y s mB P hP).comp e₀.toLinearMap).ker) :
    (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection A.polarized A.action x s mA P hP).ker =
      (RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank.fieldMarkingFirstProjection B.polarized B.action y s mB P hP).ker := by
  apply Submodule.comap_injective_of_surjective e₀.surjective
  simpa only [LinearMap.ker_comp] using heq

def markedPELFiberComparison : RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison.NativePolarizedComparison
    (A.polarized.pullback x.left) (B.polarized.pullback y.left) where
  periods := RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A.polarized A.action x B.polarized B.action y mA mB
  hodge := RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison.fieldMarkingPeriodComparison_isHodgeMap A.polarized A.action x
    B.polarized B.action y s hs rfl hdegree mA mB P hP
    (A.rosati.pullback _ _ x.left) (B.rosati.pullback _ _ y.left) hp hk
    (A.complexFiber_embedding_rank κ hκ x.left (Complex.BallPeriods.restrictComplexBase_point κ x) hP)
    (B.complexFiber_embedding_rank κ hκ y.left (Complex.BallPeriods.restrictComplexBase_point κ y) hP)
  integral := RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_integral A.polarized A.action x
    B.polarized B.action y mA mB hi
  polarization := by
    intro v w
    have h := RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_polarization A.polarized A.action x
      B.polarized B.action y mA mB hp v w
    unfold RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm at h
    exact h

theorem markedPELFiberComparison_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (markedPELFiberComparison κ hκ hP A B x y mA mB hs hdegree hi hp hk).periods (mA v) = mB v :=
  RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange.fieldMarkingPeriodComparison_marking A.polarized A.action x B.polarized B.action y mA mB v

theorem markedPELFiberComparison_action (a : NumberField.RingOfIntegers E) :
    (A.action.pullback x.left).map a ≫
      (markedPELFiberComparison κ hκ hP A B x y mA mB hs hdegree hi hp hk).algebraicIso.hom =
        (markedPELFiberComparison κ hκ hP A B x y mA mB hs hdegree hi hp hk).algebraicIso.hom ≫
          (B.action.pullback y.left).map a := by
  apply (markedPELFiberComparison κ hκ hP A B x y mA mB hs hdegree hi hp hk).algebraicIso_action
    (A.action.pullback x.left) (B.action.pullback y.left)
  intro b v
  exact RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_integer A.polarized A.action x
    B.polarized B.action y mA mB b v

variable {I : Type*} (label : I → Multiplicative (Fin (2 * (3 * s)) → ZMod N))
    (hlabel : Function.Surjective label) (v : I → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hA : ∀ i, Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint (A.polarized.pullback x.left) (label i) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized x).variety.toOver)
        ((N : ℝ)⁻¹ • (mA (v i)).val))
    (hB : ∀ i, Polarized.ComparisonMarkedLevel.polarizedNativeLevelPoint (B.polarized.pullback y.left) (label i) =
      HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation B.polarized y).variety.toOver)
        ((N : ℝ)⁻¹ • (mB (v i)).val))

def markedPELFiberIso :
    PEL.Objects.PELIso (A.pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ x)) (B.pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)) where
  polarized := (markedPELFiberComparison κ hκ hP A B x y mA mB hs hdegree hi hp hk).toLevelIso
    (Polarized.ComparisonMarkedLevel.polarizedComparison_level_of_rational_labels
      (markedPELFiberComparison κ hκ hP A B x y mA mB hs hdegree hi hp hk)
      label hlabel (fun i => mA (v i)) (fun i => mB (v i)) (N : ℝ)⁻¹ hA hB
      (fun i => markedPELFiberComparison_marking κ hκ hP A B x y mA mB hs hdegree hi hp hk (v i)))
  action := markedPELFiberComparison_action κ hκ hP A B x y mA mB hs hdegree hi hp hk

namespace FinePELModel

variable (M : Models.FinePELModel P iota N) (hM : M.IsFine)

omit [IsGalois ℚ E] in
include hM in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.point_eq_of_testFiber_iso (f : S ⟶ M.complexFiber κ) (g : T ⟶ M.complexFiber κ)
    (e : PEL.Objects.PELIso ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ x))
      ((M.complexTestFamily κ g).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y))) : x ≫ f = y ≫ g := by
  apply (M.complexPointClassEquiv κ hM).injective
  change (M.universal.pullback (M.complexPointBaseEquiv κ (x ≫ f))).classOf =
    (M.universal.pullback (M.complexPointBaseEquiv κ (y ≫ g))).classOf
  rw [← M.complexTestFamily_point_class κ f x, ← M.complexTestFamily_point_class κ g y]
  exact Quotient.sound ⟨e⟩

end FinePELModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PELComparison
