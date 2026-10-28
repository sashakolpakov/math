import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
import Mathlib.LinearAlgebra.Alternating.Basic

/-! # Intrinsic Chern Class Detection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernClassDetection.Geometric

noncomputable section

/-! Native period pairings detect the actual rational Chern class.
The proof uses the genuine period lattice, the invariant covector
comparison, and injectivity of rational-to-complex coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod

theorem nativeTwoCovector_ext (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a b : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A [⋀^Fin 2]→L[ℝ] ℂ)
    (h : ∀ v w : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, a ![v.val, w.val] = b ![v.val, w.val]) : a = b := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A
  have he (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
      AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i = (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val :=
    (Module.Basis.ofZLatticeBasis_apply ℝ _ (AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A) i).trans
      (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i).symm
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext_alternating
  intro v _hv
  have hf : (fun i : Fin 2 => AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A (v i)) =
      ![(AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A (v 0)).val, (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A (v 1)).val] := by
    funext i
    fin_cases i <;> exact he _
  change a (fun i => AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A (v i)) = b (fun i => AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A (v i))
  rw [hf]
  exact h _ _

theorem nativeChernClass_eq_of_form_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (h : AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L = AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A K) :
    AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L = AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation K := by
  have hc : AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A L = AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector A K := by
    apply nativeTwoCovector_ext A
    intro v w
    exact (AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod.nativeChernForm_covector A L v w).trans
      ((congrArg (fun B => (B v w : ℂ)) h).trans (AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod.nativeChernForm_covector A K v w).symm)
  apply AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_injective (Betti.Scheme.schemePointSpace A.toOver) 2
  exact (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).symm.injective hc

namespace AlgebraicPeriodModel
variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.nativeIntegralPeriod_bilinear_ext
    (B C : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian →ₗ[ℚ] AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian →ₗ[ℚ] ℚ)
    (h : ∀ l m : T.lattice, B (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
      C (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m)) : B = C := by
  let b := AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis M.abelian
  have hb (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom)) :
      M.nativeIntegralPeriod (M.nativeLatticeEquiv.symm (b i)) = AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis M.abelian i := by
    apply Subtype.ext
    exact (congrArg Subtype.val (M.nativeLatticeEquiv.apply_symm_apply (b i))).trans
      (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe M.abelian i).symm
  apply (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis M.abelian).ext
  intro i
  apply (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis M.abelian).ext
  intro j
  rw [← hb i, ← hb j]
  exact h _ _

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.nativeChernClass_eq_of_integral_pairing (L K : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (h : ∀ l m : T.lattice,
      AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) =
        AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian K (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m)) :
    AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation L =
      AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass M.abelian.variety.presentation K :=
  nativeChernClass_eq_of_form_eq M.abelian L K (M.nativeIntegralPeriod_bilinear_ext _ _ h)

end AlgebraicPeriodModel

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernClassDetection.Geometric
