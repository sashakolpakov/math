import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupHomologyPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CovectorPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CovectorDeterminant
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupSpanning
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing

/-! # Chern Period -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod

noncomputable section

section

/-! Linear evaluations of original degree-two classes on the native
periods and on their integration-normalized identity covectors. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

def nativeH2CovectorEvaluation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    A.variety.rationalCohomology 2 →ₗ[ℚ] ℂ := by
  let : Module ℚ (A.variety.complexCohomology 2) :=
    inferInstanceAs (Module ℚ (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyAsRational (Betti.Scheme.schemePointSpace A.toOver) 2))
  exact
  ((ContinuousAlternatingMap.apply ℝ A.variety.analyticModel ℂ ![v.val, w.val]).toLinearMap.restrictScalars ℚ).comp
    (((AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).symm.restrictScalars ℚ).toLinearMap.comp
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 2).hom)

def nativeH2PeriodEvaluation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    A.variety.rationalCohomology 2 →ₗ[ℚ] ℂ where
  toFun c := (HomologyCrossPairing.alternatingClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c
    (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w) : ℂ)
  map_add' c d := by
    simp only [HomologyCrossPairing.alternatingClassPairing, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.flip_apply, smul_eq_mul, ← CrossClassEvaluation.crossClassPairing_multiplication, map_add,
      LinearMap.add_apply, Rat.cast_mul, Rat.cast_sub, Rat.cast_add]
    ring
  map_smul' r c := by
    simp only [HomologyCrossPairing.alternatingClassPairing, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.flip_apply, smul_eq_mul, ← CrossClassEvaluation.crossClassPairing_multiplication, map_smul,
      Rat.cast_mul, Rat.cast_sub, Rat.smul_def, RingHom.id_apply]
    ring

theorem nativeH2CovectorEvaluation_cup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
    (a b : A.variety.rationalCohomology 1) :
    nativeH2CovectorEvaluation A v w (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b) =
      (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a v : ℂ) * (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b w : ℂ) -
      (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a w : ℂ) * (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b v : ℂ) := by
  change (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).symm
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 2
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b)) ![v.val, w.val] = _
  have hc : (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).symm
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 2
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b)) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (CovectorPeriods.nativeH1Covector A a) (CovectorPeriods.nativeH1Covector A b) :=
    (congrArg (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 2).symm
      (AbelianVariety.ExteriorCohomologyComplexCup.Constructions.rationalToComplex_cup (Betti.Scheme.schemePointSpace A.toOver) 1 1 a b)).trans
        (CovectorCup.nativeCovectorBetti_cup A 1 1 _ _)
  refine (congrArg (fun f : A.variety.analyticModel [⋀^Fin 2]→L[ℝ] ℂ => f ![v.val, w.val]) hc).trans ?_
  refine (CovectorDeterminant.covectorWedge_one_one (CovectorPeriods.nativeH1Covector A a) (CovectorPeriods.nativeH1Covector A b) v.val w.val).trans ?_
  exact congrArg₂ (fun x y : ℂ => x - y)
    (congrArg₂ (fun x y : ℂ => x * y) (CovectorPeriods.nativeH1Covector_period A a v) (CovectorPeriods.nativeH1Covector_period A b w))
    (congrArg₂ (fun x y : ℂ => x * y) (CovectorPeriods.nativeH1Covector_period A a w) (CovectorPeriods.nativeH1Covector_period A b v))

theorem nativeH2PeriodEvaluation_cup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
    (a b : A.variety.rationalCohomology 1) :
    nativeH2PeriodEvaluation A v w (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b) =
      (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a v : ℂ) * (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b w : ℂ) -
      (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a w : ℂ) * (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b v : ℂ) := by
  change (HomologyCrossPairing.alternatingClassPairing _ _ _ _ _ : ℂ) = _
  rw [CupHomologyPairing.alternatingClassPairing_cup]
  rw [HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A v a, HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A w b,
    HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A v b, HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A w a]
  simp only [Rat.cast_sub, Rat.cast_mul]
  ring

theorem nativeH2Evaluation_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    nativeH2CovectorEvaluation A v w = nativeH2PeriodEvaluation A v w := by
  have ht := CupSpanning.abelianH2_cup_spanned A
    (LinearMap.ker (nativeH2CovectorEvaluation A v w - nativeH2PeriodEvaluation A v w))
    (fun a b => by
      change nativeH2CovectorEvaluation A v w _ - nativeH2PeriodEvaluation A v w _ = 0
      rw [nativeH2CovectorEvaluation_cup, nativeH2PeriodEvaluation_cup, sub_self])
  ext c
  have hc : c ∈ LinearMap.ker (nativeH2CovectorEvaluation A v w - nativeH2PeriodEvaluation A v w) :=
    ht.symm ▸ Submodule.mem_top
  exact sub_eq_zero.mp hc

end

section

/-! The original singular-homology Chern pairing is exactly the actual
invariant Chern covector evaluated on native rational period vectors. -/

open _root_.CategoryTheory

theorem nativeMultiplication_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ChernPairing.nativeMultiplication A = AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A := by
  apply TopCat.ext
  intro x
  rfl

theorem nativeChernForm_covector (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AmpleChernInvariant.nativeChernCovector A L ![v.val, w.val] = (ChernPairing.nativeChernForm A L v w : ℂ) := by
  have h := DFunLike.congr_fun (nativeH2Evaluation_eq A v w)
    (ChernClasses.lineBundleChernClass A.variety.presentation L)
  change AmpleChernInvariant.nativeChernCovector A L ![v.val, w.val] =
    (HomologyCrossPairing.alternatingClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A)
      (ChernClasses.lineBundleChernClass A.variety.presentation L)
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w) : ℂ) at h
  exact h.trans (congrArg (fun m => (HomologyCrossPairing.alternatingClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) m
    (ChernClasses.lineBundleChernClass A.variety.presentation L)
    (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w) : ℂ)) (nativeMultiplication_eq A).symm)

end

/-! The original rational polarization form is nondegenerate: its
vanishing on the full period lattice forces the positive real Chern
covector to vanish on every real tangent vector. -/

def twoCovectorRight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E [⋀^Fin 2]→L[ℝ] ℂ) (u : E) : E →ₗ[ℝ] ℂ :=
  a.toContinuousMultilinearMap.toMultilinearMap.toLinearMap ![u, 0] 1

theorem twoCovectorRight_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E [⋀^Fin 2]→L[ℝ] ℂ) (u v : E) : twoCovectorRight a u v = a ![u, v] := by
  change a (Function.update ![u, 0] 1 v) = _
  congr 1
  funext i
  fin_cases i <;> simp

theorem nativeChernForm_separating (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : L.IsAmple) (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
    (hv : ∀ w, ChernPairing.nativeChernForm A L v w = 0) : v = 0 := by
  let : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
    HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full Torsion.IntrinsicTorsion.e06Input A
  have hc (w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) : AmpleChernInvariant.nativeChernCovector A L ![v.val, w.val] = 0 :=
    (nativeChernForm_covector A L v w).trans (by rw [hv w, Rat.cast_zero])
  let f := twoCovectorRight (AmpleChernInvariant.nativeChernCovector A L) v.val
  have hf : f = 0 := by
    apply (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext
    intro i
    have he : (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val = RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i :=
      (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i).trans
        (Module.Basis.ofZLatticeBasis_apply ℝ _ (Torsion.IntrinsicTorsion.periodBasis A) i).symm
    change twoCovectorRight (AmpleChernInvariant.nativeChernCovector A L) v.val (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i) = 0
    exact (twoCovectorRight_apply (AmpleChernInvariant.nativeChernCovector A L) v.val (RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i)).trans
      ((congrArg (fun w => AmpleChernInvariant.nativeChernCovector A L ![v.val, w]) he.symm).trans
        (hc (RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i)))
  have hz : v.val = 0 := AmpleChernInvariant.nativeChernCovector_separating A L hL v.val (fun w =>
    (twoCovectorRight_apply (AmpleChernInvariant.nativeChernCovector A L) v.val w).symm.trans (DFunLike.congr_fun hf w))
  exact Subtype.ext hz

theorem nativePolarizationForm_separating {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
    (hv : ∀ w, ChernPairing.nativePolarizationForm A v w = 0) : v = 0 :=
  nativeChernForm_separating
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))
    (ChernPairing.polarizationLineBundle A) (ChernPairing.polarizationLineBundle_ample A) v hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
