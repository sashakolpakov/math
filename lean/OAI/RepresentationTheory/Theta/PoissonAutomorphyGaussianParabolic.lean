import OAI.RepresentationTheory.Theta.GaussianIntegral
import OAI.RepresentationTheory.Theta.RealGenerators
import Lean.Util.CollectAxioms

/-! # Poisson Automorphy Gaussian Parabolic -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction
open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic
section

/-! Determinant and normalization of the Gaussian integral coefficient. -/

open scoped _root_.Matrix
open _root_.Matrix _root_.MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_det_realMap (L : Matrix ι ι ℝ) :
    (L.map (algebraMap ℝ ℂ)).det = (L.det : ℂ) :=
  ((algebraMap ℝ ℂ).map_det L).symm

omit [DecidableEq ι] in
theorem diagonalGaussianMass_sq (d : ι → ℝ) :
    GaussianIntegral.PoissonAutomorphyConstruction.diagonalGaussianMass d ^ 2 * (∏ i, ((d i : ℂ) + Complex.I)) =
      Complex.I ^ Fintype.card ι := by
  have hscalar (i : ι) :
      (((Real.pi : ℂ) / (-((Real.pi : ℂ) * Complex.I) * ((d i : ℂ) + Complex.I))) ^
        (1 / 2 : ℂ)) ^ 2 * ((d i : ℂ) + Complex.I) = Complex.I := by
    rw [one_div, Complex.cpow_ofNat_inv_pow]
    field_simp [GaussianIntegral.PoissonAutomorphyConstruction.diagonal_siegel_entry_ne_zero (d i), Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    simp
  rw [GaussianIntegral.PoissonAutomorphyConstruction.diagonalGaussianMass, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  simp only [hscalar, Finset.prod_const, Finset.card_univ]

theorem gaussianMass_sq_mul_det (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass Z ^ 2 * Z.matrix.det = Complex.I ^ Fintype.card ι := by
  obtain ⟨L, d, hL, hdiag⟩ := PoissonAutomorphyGaussianPoisson.Construction.siegel_real_diagonalization Z
  have hdet : (L.det : ℂ) ^ 2 * Z.matrix.det = ∏ i, ((d i : ℂ) + Complex.I) := by
    have h := congrArg Matrix.det hdiag
    simp only [Matrix.det_mul, Matrix.det_transpose, complex_det_realMap, Matrix.det_diagonal] at h
    convert h using 1
    ring
  have hmass : GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass Z = ((|L.det| : ℝ) : ℂ) * GaussianIntegral.PoissonAutomorphyConstruction.diagonalGaussianMass d := by
    rw [GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass, GaussianIntegral.PoissonAutomorphyConstruction.gaussian_integral_diagonalized Z L d hL hdiag]
    simp
  have habs : (((|L.det| : ℝ) : ℂ)) ^ 2 = (L.det : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  rw [hmass, mul_pow, habs]
  calc
    _ = GaussianIntegral.PoissonAutomorphyConstruction.diagonalGaussianMass d ^ 2 * ((L.det : ℂ) ^ 2 * Z.matrix.det) := by ring
    _ = _ := by rw [hdet, diagonalGaussianMass_sq]

theorem gaussianMass_ne_zero (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass Z ≠ 0 := by
  intro h
  have heq := gaussianMass_sq_mul_det Z
  rw [h, zero_pow (by decide), zero_mul] at heq
  exact (pow_ne_zero _ Complex.I_ne_zero) heq.symm

theorem siegel_matrix_det_ne_zero (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : Z.matrix.det ≠ 0 := by
  intro h
  have heq := gaussianMass_sq_mul_det Z
  rw [h, mul_zero] at heq
  exact (pow_ne_zero _ Complex.I_ne_zero) heq.symm

theorem gaussianMass_sq (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass Z ^ 2 = Complex.I ^ Fintype.card ι * Z.matrix.det⁻¹ := by
  apply (mul_right_cancel₀ (siegel_matrix_det_ne_zero Z))
  rw [gaussianMass_sq_mul_det, mul_assoc, inv_mul_cancel₀ (siegel_matrix_det_ne_zero Z), mul_one]

theorem gaussianFunction_base (x : ι → ℝ) :
    PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)) 0 x =
      Complex.exp (-((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2)) := by
  rw [PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix]
  simp only [PoissonAutomorphyNormalizationData.toSiegel, PoissonAutomorphyNormalizationData.basePeriod, Matrix.mulVec_diagonal, GaussianIntegral.PoissonAutomorphyConstruction.complexVector, dotProduct,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf
  simp

theorem gaussianMass_base : GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)) = 1 := by
  unfold GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass
  simp_rw [gaussianFunction_base, Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.exp_sum]
  calc
    _ = ∏ _i : ι, ∫ t : ℝ, Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2)) := by
      convert! integral_fintype_prod_volume_eq_prod
        (fun _i : ι => fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * (t : ℂ) ^ 2))) using 1
    _ = _ := by simp only [RealGenerators.PoissonAutomorphyConstruction.scalar_standard_gaussian_integral, Finset.prod_const_one]

end

section

/-! Continuous dependence of the Gaussian integral on its Siegel parameter. -/

open scoped _root_.Matrix.Norms.Elementwise
open _root_.MeasureTheory Filter _root_.Topology

variable {ι : Type*} [Fintype ι]

def matrixPhaseLinear : Matrix ι ι ℂ →ₗ[ℝ] (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ where
  toFun := AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm
  map_add' M N := by
    ext x y
    simp only [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib,
      add_apply]
  map_smul' r M := by
    ext x y
    simp only [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, RingHom.id_apply, Matrix.smul_apply,
      _root_.smul_apply, Complex.real_smul, Finset.mul_sum,
      mul_comm, mul_left_comm]

theorem continuous_matrixPhase : Continuous (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (ι := ι)) := by
  change Continuous (matrixPhaseLinear (ι := ι))
  exact LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := Matrix ι ι ℂ)
    (F' := (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) (matrixPhaseLinear (ι := ι))

theorem integrable_sup_gaussian (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ι → ℝ => Real.exp (-a * ‖x‖ ^ 2)) := by
  let b := a / ((Fintype.card ι : ℝ) + 1)
  have hb : 0 < b := div_pos ha (by positivity)
  have hp : Integrable (fun x : ι → ℝ => Real.exp (-b * ∑ i, x i ^ 2)) := by
    have h := Integrable.fintype_prod (fun _i : ι => integrable_exp_neg_mul_sq hb)
    simpa only [← Real.exp_sum, ← Finset.mul_sum] using! h
  apply hp.mono' (by fun_prop)
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hs := PoissonAutomorphyGaussianPoisson.Construction.coordinate_sum_sq_le x
  have heq : b * ((Fintype.card ι : ℝ) + 1) = a := div_mul_cancel₀ a (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hs hb.le, sq_nonneg ‖x‖]

theorem gaussianFunction_continuous_parameter (z : ι → ℂ) (x : ι → ℝ) :
    Continuous (fun Z : PoissonAutomorphyNormalizationData.Domain ι => PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction (PoissonAutomorphyNormalizationData.toSiegel Z) z x) := by
  unfold PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent
  change Continuous (fun Z : PoissonAutomorphyNormalizationData.Domain ι => Complex.exp ((Real.pi : ℂ) * Complex.I *
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.val x x + (2 * (Real.pi : ℂ) * Complex.I) * AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι x z))
  have h : Continuous (fun Z : PoissonAutomorphyNormalizationData.Domain ι => AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.val x x) :=
    (AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseEvaluation x).continuous.comp (continuous_matrixPhase.comp continuous_subtype_val)
  exact ((h.const_mul _).add continuous_const).cexp

theorem gaussianMass_continuous : Continuous (fun Z : PoissonAutomorphyNormalizationData.Domain ι => GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass (PoissonAutomorphyNormalizationData.toSiegel Z)) := by
  let : FirstCountableTopology (Matrix ι ι ℂ) :=
    inferInstanceAs (FirstCountableTopology (ι → ι → ℂ))
  let : FirstCountableTopology (PoissonAutomorphyNormalizationData.Domain ι) :=
    inferInstanceAs (FirstCountableTopology {M : Matrix ι ι ℂ // M ∈ PoissonAutomorphyNormalizationData.siegelSet ι})
  apply continuous_iff_continuousAt.mpr
  intro Z
  let a := Real.pi * ((PoissonAutomorphyNormalizationData.toSiegel Z).phase.lowerBound / 2)
  have ha : 0 < a := mul_pos Real.pi_pos (half_pos (PoissonAutomorphyNormalizationData.toSiegel Z).phase.lowerBound_pos)
  have hphase : Continuous (fun W : PoissonAutomorphyNormalizationData.Domain ι => AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm W.val) :=
    continuous_matrixPhase.comp continuous_subtype_val
  have hnear := hphase.continuousAt.eventually
    (eventually_norm_sub_lt (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.val) (half_pos (PoissonAutomorphyNormalizationData.toSiegel Z).phase.lowerBound_pos))
  apply continuousAt_of_dominated (bound := fun x : ι → ℝ => Real.exp (-a * ‖x‖ ^ 2))
  · apply Eventually.of_forall
    intro W
    exact (PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent_temperate (PoissonAutomorphyNormalizationData.toSiegel W) 0).1.continuous.cexp.aestronglyMeasurable
  · filter_upwards [hnear] with W hW
    refine ae_of_all _ fun x => ?_
    have h := (PoissonAutomorphyNormalizationData.toSiegel Z).phase.nearby_phase_gaussian_bound (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm W.val) hW.le x
    simpa only [PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent, map_zero, mul_zero, add_zero, a,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase, PoissonAutomorphyNormalizationData.toSiegel] using h
  · exact integrable_sup_gaussian a ha
  · exact ae_of_all _ fun x => (gaussianFunction_continuous_parameter 0 x).continuousAt

end

section

/-! The normalized Fourier generator on the full Siegel Gaussian family. -/

open scoped _root_.Matrix
open _root_.Matrix _root_.MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weyl_complex_blocks :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).complexify.A = 0 ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).complexify.B = -1 ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).complexify.C = 1 ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).complexify.D = 0 := by
  simp [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, PoissonAutomorphyNormalizationData.realBlocks, PoissonAutomorphyNormalizationData.blocks, PoissonAutomorphyNormalizationData.mapSp, Generators.PoissonAutomorphyConstruction.weyl,
    Matrix.fromBlocks_map]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem weyl_denominator (Z : Matrix ι ι ℂ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).complexify.denominator Z = Z := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, weyl_complex_blocks.2.2.1, weyl_complex_blocks.2.2.2,
    one_mul, add_zero]

theorem weyl_transform_matrix (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).transformSiegel Z).matrix = -Z.matrix⁻¹ := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.transformSiegel_matrix, weyl_complex_blocks.1,
    weyl_complex_blocks.2.1, weyl_complex_blocks.2.2.1, weyl_complex_blocks.2.2.2]
  simp

theorem weyl_jacobi (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).jacobiChange Z z = Z.matrix⁻¹.transpose *ᵥ z := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, weyl_denominator]

theorem weyl_correction (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).thetaCorrectionForm Z z z =
      (Real.pi : ℂ) * Complex.I * (z ⬝ᵥ (Z.matrix⁻¹ *ᵥ z)) := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply, weyl_denominator,
    weyl_complex_blocks.2.2.1, mul_one]

theorem weyl_gaussian_coefficient (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ * GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass Z =
      (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z)⁻¹ := by
  let h := PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι))
  have hs : h ^ 2 = Complex.I ^ Fintype.card ι := by
    rw [PoissonAutomorphyNormalizationData.halfDet_sq, weyl_denominator]
    simp only [PoissonAutomorphyNormalizationData.toSiegel, PoissonAutomorphyNormalizationData.basePeriod, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
  let f : C(PoissonAutomorphyNormalizationData.Domain ι, ℂ) :=
    ⟨fun W => h * (GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass (PoissonAutomorphyNormalizationData.toSiegel W))⁻¹,
      continuous_const.mul (gaussianMass_continuous.inv₀ fun W => gaussianMass_ne_zero (PoissonAutomorphyNormalizationData.toSiegel W))⟩
  have heq := PoissonAutomorphyNormalizationData.halfDetDomain_unique (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) f (fun W => ?_) (by
    change h * (GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ = _
    rw [gaussianMass_base, inv_one, mul_one]
    rfl)
  · have hW := heq (PoissonAutomorphyNormalizationData.ofSiegel Z)
    change h * (GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass Z)⁻¹ = PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z at hW
    rw [← hW, _root_.mul_inv_rev, inv_inv]
    exact mul_comm _ _
  · change (h * (GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass (PoissonAutomorphyNormalizationData.toSiegel W))⁻¹) ^ 2 = _
    rw [mul_pow, inv_pow, hs, ← gaussianMass_sq_mul_det (PoissonAutomorphyNormalizationData.toSiegel W)]
    change GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass (PoissonAutomorphyNormalizationData.toSiegel W) ^ 2 * (PoissonAutomorphyNormalizationData.toSiegel W).matrix.det *
      (GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass (PoissonAutomorphyNormalizationData.toSiegel W) ^ 2)⁻¹ = ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).complexify.denominator W.val).det
    rw [weyl_denominator, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ (gaussianMass_ne_zero _)), one_mul]
    rfl

theorem fourier_gaussian_integral (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) :
    PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume (PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z) x =
      GaussianIntegral.PoissonAutomorphyConstruction.gaussianMass Z * Complex.exp (-(Real.pi : ℂ) * Complex.I *
        ((z - GaussianIntegral.PoissonAutomorphyConstruction.complexVector x) ⬝ᵥ (Z.matrix⁻¹ *ᵥ (z - GaussianIntegral.PoissonAutomorphyConstruction.complexVector x)))) := by
  have hfun : (fun y => PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z y * PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, x i * y i))) =
      PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z (z - GaussianIntegral.PoissonAutomorphyConstruction.complexVector x) := by
    funext y
    rw [PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, PoissonAutomorphyNormalizationData.standardRealCharacter_apply, ← Complex.exp_add, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction,
      GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix, GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix]
    congr 1
    simp only [dotProduct, Pi.sub_apply, GaussianIntegral.PoissonAutomorphyConstruction.complexVector, mul_sub, Finset.sum_sub_distrib]
    push_cast
    simp only [mul_comm (x _ : ℂ) (y _ : ℂ)]
    ring
  rw [PoissonAutomorphyNormalizationData.fourier, hfun, GaussianIntegral.PoissonAutomorphyConstruction.gaussian_integral]

theorem weyl_gaussian_exponent (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) :
    -(Real.pi : ℂ) * Complex.I *
        ((z - GaussianIntegral.PoissonAutomorphyConstruction.complexVector x) ⬝ᵥ (Z.matrix⁻¹ *ᵥ (z - GaussianIntegral.PoissonAutomorphyConstruction.complexVector x))) =
      -(PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).thetaCorrectionForm Z z z +
        PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).transformSiegel Z)
          ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).jacobiChange Z z) x := by
  rw [weyl_correction, GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix, weyl_transform_matrix, weyl_jacobi]
  have hcross : z ⬝ᵥ (Z.matrix⁻¹ *ᵥ GaussianIntegral.PoissonAutomorphyConstruction.complexVector x) =
      GaussianIntegral.PoissonAutomorphyConstruction.complexVector x ⬝ᵥ (Z.matrix⁻¹ *ᵥ z) := by
    simpa only [Z.symmetric.inv.eq] using
      (Matrix.dotProduct_transpose_mulVec Z.matrix⁻¹ (GaussianIntegral.PoissonAutomorphyConstruction.complexVector x) z).symm
  simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, Matrix.neg_mulVec,
    dotProduct_neg, Z.symmetric.inv.eq, hcross]
  ring

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem realAction_weyl_gaussian (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.weyl ι)) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z) =
      ((PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z)⁻¹ * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z z)⁻¹) •
        PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).transformSiegel Z)
          ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).jacobiChange Z z) := by
  apply Subtype.ext
  funext x
  change (D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.weyl ι)) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z)).val x =
    ((PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z)⁻¹ * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z z)⁻¹) *
      PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).transformSiegel Z)
        ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)).jacobiChange Z z) x
  rw [RealGenerators.PoissonAutomorphyConstruction.realAction_weyl]
  change (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ *
    PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume (PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z) x = _
  rw [fourier_gaussian_integral, ← mul_assoc, weyl_gaussian_coefficient,
    weyl_gaussian_exponent, Complex.exp_add, mul_assoc]
  simp only [PoissonAutomorphyNormalizationData.quadraticFactor, Complex.exp_neg, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction]

end

section

/-! Composition of the Siegel and Jacobi substitutions and their correction factors. -/

open scoped _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem symplecticBlocks_ext {K : Type*} [CommRing K] {g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι K}
    (hA : g.A = h.A) (hB : g.B = h.B) (hC : g.C = h.C) (hD : g.D = h.D) : g = h := by
  cases g
  cases h
  simp_all

def composeBlocks {K : Type*} [CommRing K] (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι K) : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι K where
  A := g.A * h.A + g.B * h.C
  B := g.A * h.B + g.B * h.D
  C := g.C * h.A + g.D * h.C
  D := g.C * h.B + g.D * h.D
  symplectic := by
    rw [← Matrix.fromBlocks_multiply]
    exact (Matrix.symplecticGroup ι K).mul_mem g.symplectic h.symplectic

theorem complexify_composeBlocks (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) :
    (composeBlocks g h).complexify = composeBlocks g.complexify h.complexify := by
  apply symplecticBlocks_ext <;> ext i j <;>
    simp [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, composeBlocks, Matrix.mul_apply, Matrix.map_apply]

theorem blocks_mul {K : Type*} [CommRing K] (γ δ : PoissonAutomorphyNormalizationData.Sp ι K) :
    PoissonAutomorphyNormalizationData.blocks (γ * δ) = composeBlocks (PoissonAutomorphyNormalizationData.blocks γ) (PoissonAutomorphyNormalizationData.blocks δ) := by
  have h : (γ * δ).val = Matrix.fromBlocks
      (γ.val.toBlocks₁₁ * δ.val.toBlocks₁₁ + γ.val.toBlocks₁₂ * δ.val.toBlocks₂₁)
      (γ.val.toBlocks₁₁ * δ.val.toBlocks₁₂ + γ.val.toBlocks₁₂ * δ.val.toBlocks₂₂)
      (γ.val.toBlocks₂₁ * δ.val.toBlocks₁₁ + γ.val.toBlocks₂₂ * δ.val.toBlocks₂₁)
      (γ.val.toBlocks₂₁ * δ.val.toBlocks₁₂ + γ.val.toBlocks₂₂ * δ.val.toBlocks₂₂) := by
    rw [← Matrix.fromBlocks_multiply, Matrix.fromBlocks_toBlocks, Matrix.fromBlocks_toBlocks]
    rfl
  apply symplecticBlocks_ext <;> simp only [PoissonAutomorphyNormalizationData.blocks, composeBlocks, h,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]

theorem realBlocks_mul (γ δ : PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    PoissonAutomorphyNormalizationData.realBlocks (γ * δ) = composeBlocks (PoissonAutomorphyNormalizationData.realBlocks γ) (PoissonAutomorphyNormalizationData.realBlocks δ) := by
  unfold PoissonAutomorphyNormalizationData.realBlocks
  rw [map_mul, blocks_mul]

theorem compose_denominator (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℂ) (Z : Matrix ι ι ℂ)
    (hJ : IsUnit (h.denominator Z).det) :
    (composeBlocks g h).denominator Z = g.denominator (h.fractional Z) * h.denominator Z := by
  have hfrac := h.fractional_mul_denominator Z hJ
  simp only [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, Matrix.add_mul, Matrix.mul_assoc] at hfrac ⊢
  rw [hfrac]
  simp only [composeBlocks, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator]
  noncomm_ring

theorem compose_numerator (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℂ) (Z : Matrix ι ι ℂ)
    (hJ : IsUnit (h.denominator Z).det) :
    (composeBlocks g h).numerator Z = g.numerator (h.fractional Z) * h.denominator Z := by
  have hfrac := h.fractional_mul_denominator Z hJ
  simp only [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator, Matrix.add_mul, Matrix.mul_assoc]
  rw [hfrac]
  simp only [composeBlocks, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator]
  noncomm_ring

theorem compose_fractional (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℂ) (Z : Matrix ι ι ℂ)
    (hJ : IsUnit (h.denominator Z).det) :
    (composeBlocks g h).fractional Z = g.fractional (h.fractional Z) := by
  unfold AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.fractional
  rw [compose_numerator g h Z hJ, compose_denominator g h Z hJ, Matrix.mul_inv_rev]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (g.numerator _),
    Matrix.mul_nonsing_inv _ hJ, mul_one]
  rfl

omit [DecidableEq ι] in
theorem siegelMatrix_ext {Z W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι} (h : Z.matrix = W.matrix) : Z = W := by
  cases Z
  cases W
  simp_all

theorem compose_transformSiegel (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    (composeBlocks g h).transformSiegel Z = g.transformSiegel (h.transformSiegel Z) := by
  apply siegelMatrix_ext
  change (composeBlocks g h).complexify.fractional Z.matrix =
    g.complexify.fractional (h.complexify.fractional Z.matrix)
  rw [complexify_composeBlocks, compose_fractional _ _ _ (h.denominator_det_isUnit Z)]

theorem compose_jacobiChange (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    (composeBlocks g h).jacobiChange Z z =
      g.jacobiChange (h.transformSiegel Z) (h.jacobiChange Z z) := by
  simp only [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply]
  rw [complexify_composeBlocks, compose_denominator _ _ _ (h.denominator_det_isUnit Z),
    Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mulVec_mulVec]
  rfl

theorem compose_correction (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    (composeBlocks g h).thetaCorrectionForm Z z z = h.thetaCorrectionForm Z z z +
      g.thetaCorrectionForm (h.transformSiegel Z) (h.jacobiChange Z z) (h.jacobiChange Z z) := by
  have hk := (composeBlocks g h).completion_correction_identity Z z
  have hh := h.completion_correction_identity Z z
  have hg := g.completion_correction_identity (h.transformSiegel Z) (h.jacobiChange Z z)
  rw [compose_transformSiegel, compose_jacobiChange] at hk
  linear_combination hk - hh - hg

theorem compose_quadraticFactor (g h : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    PoissonAutomorphyNormalizationData.quadraticFactor (composeBlocks g h) Z z = PoissonAutomorphyNormalizationData.quadraticFactor h Z z *
      PoissonAutomorphyNormalizationData.quadraticFactor g (h.transformSiegel Z) (h.jacobiChange Z z) := by
  unfold PoissonAutomorphyNormalizationData.quadraticFactor
  rw [compose_correction, Complex.exp_add]

def transformDomain (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : PoissonAutomorphyNormalizationData.Domain ι) : PoissonAutomorphyNormalizationData.Domain ι :=
  PoissonAutomorphyNormalizationData.ofSiegel (g.transformSiegel (PoissonAutomorphyNormalizationData.toSiegel Z))

theorem transformDomain_continuous (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) : Continuous (transformDomain g) := by
  apply Continuous.subtype_mk
  change Continuous (fun Z : PoissonAutomorphyNormalizationData.Domain ι => g.complexify.numerator Z.val *
    (g.complexify.denominator Z.val)⁻¹)
  apply Continuous.mul
  · unfold AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator
    fun_prop
  · apply continuous_iff_continuousAt.mpr
    intro Z
    apply (continuousAt_matrix_inv _ ?_).comp
      (show ContinuousAt (fun W : PoissonAutomorphyNormalizationData.Domain ι => g.complexify.denominator W.val) Z by
        unfold AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator
        fun_prop)
    rw [show (Ring.inverse : ℂ → ℂ) = (fun c => c⁻¹) from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ (g.denominator_det_isUnit (PoissonAutomorphyNormalizationData.toSiegel Z)).ne_zero

end

section

/-! The real triangular generators, obtained from the prescribed rational splitting. -/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem adelicAtReal_mulVec (A : Matrix ι ι ℚ) (x : ι → ℝ) :
    A.map (algebraMap ℚ PoissonAutomorphyNormalizationData.AQ) *ᵥ RealGenerators.PoissonAutomorphyConstruction.adelicAtReal x =
      RealGenerators.PoissonAutomorphyConstruction.adelicAtReal (A.map (algebraMap ℚ ℝ) *ᵥ x) := by
  funext i
  apply Prod.ext <;> simp [RealGenerators.PoissonAutomorphyConstruction.adelicAtReal, Matrix.mulVec, dotProduct, Prod.fst_sum, Prod.snd_sum]

omit [DecidableEq ι] in
theorem adelicAtReal_quadratic (B : Matrix ι ι ℚ) (x : ι → ℝ) :
    algebraMap ℚ PoissonAutomorphyNormalizationData.AQ (1 / 2) * (RealGenerators.PoissonAutomorphyConstruction.adelicAtReal x ⬝ᵥ (B.map (algebraMap ℚ PoissonAutomorphyNormalizationData.AQ) *ᵥ RealGenerators.PoissonAutomorphyConstruction.adelicAtReal x)) =
      ((1 / 2 : ℝ) * (x ⬝ᵥ (B.map (algebraMap ℚ ℝ) *ᵥ x)), 0) := by
  rw [adelicAtReal_mulVec]
  apply Prod.ext <;> simp [RealGenerators.PoissonAutomorphyConstruction.adelicAtReal, dotProduct, Prod.fst_sum, Prod.snd_sum]

omit [DecidableEq ι] in
theorem tensor_integralTest_atReal (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (x : ι → ℝ) :
    (PoissonAutomorphyNormalizationData.tensor f PoissonAutomorphyFiniteFourier.Construction.integralTestFunction).val (RealGenerators.PoissonAutomorphyConstruction.adelicAtReal x) = f.val x := by
  change f.val x * PoissonAutomorphyFiniteFourier.Construction.integralIndicator 0 = f.val x
  rw [PoissonAutomorphyFiniteFourier.Construction.integralIndicator_of_mem PoissonAutomorphyFiniteFourier.Construction.integralVectors.zero_mem, mul_one]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem realAction_upper (B : Matrix ι ι ℚ) (hB : B.IsSymm)
    (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (x : ι → ℝ) :
    (D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.upper B hB)) f).val x =
      (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ *
        (PoissonAutomorphyNormalizationData.standardRealCharacter ((1 / 2 : ℝ) * (x ⬝ᵥ (B.map (algebraMap ℚ ℝ) *ᵥ x))) * f.val x) := by
  apply RealGenerators.PoissonAutomorphyConstruction.realAction_formula_from_vacuum D (Generators.PoissonAutomorphyConstruction.upper B hB) _ ?_ ?_
  · intro F y
    change (D.adelic.action (D.rationalSplit (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyNormalizationData.tensor F PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)).val _ = _
    rw [D.rational_quadratic (Generators.PoissonAutomorphyConstruction.upper B hB) B hB rfl, adelicAtReal_quadratic,
      D.character_real, tensor_integralTest_atReal]
  · simp only [zero_dotProduct, mul_zero, AddChar.map_zero_eq_one, one_mul, RealGenerators.PoissonAutomorphyConstruction.vacuum_zero]

theorem realAction_levi (A : (Matrix ι ι ℚ)ˣ) (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (x : ι → ℝ) :
    (D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.levi A)) f).val x =
      (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ *
        f.val (A.val.transpose.map (algebraMap ℚ ℝ) *ᵥ x) := by
  apply RealGenerators.PoissonAutomorphyConstruction.realAction_formula_from_vacuum D (Generators.PoissonAutomorphyConstruction.levi A) _ ?_ ?_
  · intro F y
    change (D.adelic.action (D.rationalSplit (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyNormalizationData.tensor F PoissonAutomorphyFiniteFourier.Construction.integralTestFunction)).val _ = _
    rw [D.rational_linear (Generators.PoissonAutomorphyConstruction.levi A) A rfl, adelicAtReal_mulVec, tensor_integralTest_atReal]
  · rw [Matrix.mulVec_zero, RealGenerators.PoissonAutomorphyConstruction.vacuum_zero]

end

section

/-! Explicit Siegel substitutions for the upper and Levi generators. -/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem real_complex_matrix_cast (M : Matrix ι ι ℚ) :
    (M.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) = M.map (algebraMap ℚ ℂ) := by
  ext i j
  simp

theorem upper_complex_blocks (B : Matrix ι ι ℚ) (hB : B.IsSymm) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).complexify.A = 1 ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).complexify.B = B.map (algebraMap ℚ ℂ) ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).complexify.C = 0 ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).complexify.D = 1 := by
  simp [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, PoissonAutomorphyNormalizationData.realBlocks, PoissonAutomorphyNormalizationData.blocks, PoissonAutomorphyNormalizationData.mapSp, Generators.PoissonAutomorphyConstruction.upper, Matrix.fromBlocks_map]
  ext i j
  simp

theorem upper_denominator (B : Matrix ι ι ℚ) (hB : B.IsSymm) (Z : Matrix ι ι ℂ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).complexify.denominator Z = 1 := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, (upper_complex_blocks B hB).2.2.1,
    (upper_complex_blocks B hB).2.2.2, zero_mul, zero_add]

theorem upper_transform_matrix (B : Matrix ι ι ℚ) (hB : B.IsSymm) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).transformSiegel Z).matrix = Z.matrix + B.map (algebraMap ℚ ℂ) := by
  change (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).complexify.numerator Z.matrix *
    ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).complexify.denominator Z.matrix)⁻¹ = _
  rw [upper_denominator, inv_one, mul_one, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator,
    (upper_complex_blocks B hB).1, (upper_complex_blocks B hB).2.1, one_mul]

theorem upper_jacobi (B : Matrix ι ι ℚ) (hB : B.IsSymm) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).jacobiChange Z z = z := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, upper_denominator, inv_one,
    Matrix.transpose_one, Matrix.one_mulVec]

theorem correction_of_C_zero (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (hC : g.complexify.C = 0)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : g.thetaCorrectionForm Z z z = 0 := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply, hC, mul_zero, Matrix.zero_mulVec,
    dotProduct_zero, mul_zero]

def complexMatrixUnit (A : (Matrix ι ι ℚ)ˣ) : (Matrix ι ι ℂ)ˣ :=
  Units.map (algebraMap ℚ ℂ).mapMatrix.toMonoidHom A

theorem complexMatrixUnit_val (A : (Matrix ι ι ℚ)ˣ) :
    (complexMatrixUnit A).val = A.val.map (algebraMap ℚ ℂ) := rfl

theorem levi_complex_blocks (A : (Matrix ι ι ℚ)ˣ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.A = (complexMatrixUnit A).val ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.B = 0 ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.C = 0 ∧
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.D = ((complexMatrixUnit A)⁻¹).val.transpose := by
  simp [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, PoissonAutomorphyNormalizationData.realBlocks, PoissonAutomorphyNormalizationData.blocks, PoissonAutomorphyNormalizationData.mapSp, Generators.PoissonAutomorphyConstruction.levi, Matrix.fromBlocks_map,
    complexMatrixUnit, Matrix.transpose_map]
  constructor <;> ext i j <;> simp

theorem levi_denominator (A : (Matrix ι ι ℚ)ˣ) (Z : Matrix ι ι ℂ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.denominator Z = ((complexMatrixUnit A)⁻¹).val.transpose := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, (levi_complex_blocks A).2.2.1,
    (levi_complex_blocks A).2.2.2, zero_mul, zero_add]

theorem levi_denominator_inv (A : (Matrix ι ι ℚ)ˣ) (Z : Matrix ι ι ℂ) :
    ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.denominator Z)⁻¹ = (complexMatrixUnit A).val.transpose := by
  rw [levi_denominator]
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem levi_transform_matrix (A : (Matrix ι ι ℚ)ˣ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).transformSiegel Z).matrix =
      (complexMatrixUnit A).val * Z.matrix * (complexMatrixUnit A).val.transpose := by
  change (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.numerator Z.matrix *
    ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).complexify.denominator Z.matrix)⁻¹ = _
  rw [levi_denominator_inv, AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator,
    (levi_complex_blocks A).1, (levi_complex_blocks A).2.1, add_zero]

theorem levi_jacobi (A : (Matrix ι ι ℚ)ˣ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).jacobiChange Z z = (complexMatrixUnit A).val *ᵥ z := by
  rw [AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, levi_denominator_inv, Matrix.transpose_transpose]

end

section

/-! Gaussian formulas for the real upper and Levi generators. -/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem complexQuadratic_realMap (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    GaussianIntegral.PoissonAutomorphyConstruction.complexVector x ⬝ᵥ (M.map (algebraMap ℝ ℂ) *ᵥ GaussianIntegral.PoissonAutomorphyConstruction.complexVector x) =
      ((x ⬝ᵥ (M *ᵥ x) : ℝ) : ℂ) := by
  simp [GaussianIntegral.PoissonAutomorphyConstruction.complexVector, dotProduct, Matrix.mulVec]

theorem upper_gaussian_function (B : Matrix ι ι ℚ) (hB : B.IsSymm)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) :
    PoissonAutomorphyNormalizationData.standardRealCharacter ((1 / 2 : ℝ) * (x ⬝ᵥ (B.map (algebraMap ℚ ℝ) *ᵥ x))) *
      PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z x =
      PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).transformSiegel Z)
        ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).jacobiChange Z z) x := by
  rw [PoissonAutomorphyNormalizationData.standardRealCharacter_apply, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, ← Complex.exp_add, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction,
    GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix, GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix, upper_transform_matrix, upper_jacobi,
    Matrix.add_mulVec, dotProduct_add, ← real_complex_matrix_cast B, complexQuadratic_realMap]
  congr 1
  push_cast
  ring

theorem levi_gaussian_function (A : (Matrix ι ι ℚ)ˣ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) :
    PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z (A.val.transpose.map (algebraMap ℚ ℝ) *ᵥ x) =
      PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).transformSiegel Z)
        ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).jacobiChange Z z) x := by
  have hcast : (A.val.transpose.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) =
      (complexMatrixUnit A).val.transpose := by
    rw [real_complex_matrix_cast, complexMatrixUnit_val, Matrix.transpose_map]
  simp only [PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction]
  rw [GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix, GaussianIntegral.PoissonAutomorphyConstruction.gaussianExponent_matrix, GaussianIntegral.PoissonAutomorphyConstruction.complexVector_mulVec, hcast,
    AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.bilinear_matrix_pullback, Matrix.transpose_transpose, levi_transform_matrix, levi_jacobi]
  congr 2
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem realAction_upper_gaussian (B : Matrix ι ι ℚ) (hB : B.IsSymm)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z) =
      (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ •
        PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).transformSiegel Z)
          ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).jacobiChange Z z) := by
  apply Subtype.ext
  funext x
  change (D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z)).val x =
    (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ *
      PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).transformSiegel Z)
        ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)).jacobiChange Z z) x
  rw [realAction_upper, PoissonAutomorphyGaussianPoisson.Construction.gaussianTest_apply, upper_gaussian_function]

theorem realAction_levi_gaussian (A : (Matrix ι ι ℚ)ˣ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z) =
      (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ •
        PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).transformSiegel Z)
          ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).jacobiChange Z z) := by
  apply Subtype.ext
  funext x
  change (D.real.action (D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z)).val x =
    (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ *
      PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).transformSiegel Z)
        ((PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)).jacobiChange Z z) x
  rw [realAction_levi, PoissonAutomorphyGaussianPoisson.Construction.gaussianTest_apply, levi_gaussian_function]

end

section

/-! A multiplication-only induction principle for the rational symplectic generators. -/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem upper_inv (B : Matrix ι ι ℚ) (hB : B.IsSymm) :
    (Generators.PoissonAutomorphyConstruction.upper B hB)⁻¹ = Generators.PoissonAutomorphyConstruction.upper (-B) hB.neg := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change Matrix.fromBlocks 1 (-B) 0 1 * Matrix.fromBlocks 1 B 0 1 = 1
  simp [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem weyl_inv_eq_cube : (Generators.PoissonAutomorphyConstruction.weyl ι)⁻¹ = Generators.PoissonAutomorphyConstruction.weyl ι * Generators.PoissonAutomorphyConstruction.weyl ι * Generators.PoissonAutomorphyConstruction.weyl ι := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change ((Matrix.fromBlocks 0 (-1) 1 0 * Matrix.fromBlocks 0 (-1) 1 0) *
    Matrix.fromBlocks 0 (-1) 1 0) * Matrix.fromBlocks 0 (-1) 1 0 = (1 : Matrix (Sum ι ι) (Sum ι ι) ℚ)
  simp [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem rational_generator_induction (P : PoissonAutomorphyNormalizationData.Sp ι ℚ → Prop)
    (hmul : ∀ γ δ, P γ → P δ → P (γ * δ))
    (hU : ∀ (B : Matrix ι ι ℚ) (hB : B.IsSymm), P (Generators.PoissonAutomorphyConstruction.upper B hB))
    (hM : ∀ A : (Matrix ι ι ℚ)ˣ, P (Generators.PoissonAutomorphyConstruction.levi A))
    (hW : P (Generators.PoissonAutomorphyConstruction.weyl ι)) (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) : P γ := by
  have hWi : P (Generators.PoissonAutomorphyConstruction.weyl ι)⁻¹ := by
    rw [weyl_inv_eq_cube]
    exact hmul _ _ (hmul _ _ hW hW) hW
  have hL : ∀ (B : Matrix ι ι ℚ) (hB : B.IsSymm), P (Generators.PoissonAutomorphyConstruction.lower B hB) := by
    intro B hB
    rw [Generators.PoissonAutomorphyConstruction.lower_conjugation]
    exact hmul _ _ (hmul _ _ hW (hU (-B) hB.neg)) hWi
  obtain ⟨X, hX, hdet⟩ := Generators.PoissonAutomorphyConstruction.exists_upper_bigCell γ
  let f := Generators.PoissonAutomorphyConstruction.upper X hX * γ
  obtain ⟨A, hA⟩ := (Matrix.isUnit_iff_isUnit_det f.val.toBlocks₁₁).mpr hdet
  have hmatrix : Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁ f.val.toBlocks₂₂ = f.val := by
    rw [hA, Matrix.fromBlocks_toBlocks]
  have hs : Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁ f.val.toBlocks₂₂ ∈
      Matrix.symplecticGroup ι ℚ := by
    rw [hmatrix]
    exact f.property
  have hf : P f := by
    have heq : f = ⟨Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁ f.val.toBlocks₂₂, hs⟩ :=
      Subtype.ext hmatrix.symm
    rw [heq, Generators.PoissonAutomorphyConstruction.bigCell_factorization A _ _ _ hs]
    exact hmul _ _ (hmul _ _ (hL _ _) (hM A)) (hU _ _)
  have hi : P (Generators.PoissonAutomorphyConstruction.upper X hX)⁻¹ := by rw [upper_inv]; exact hU _ _
  simpa only [f, inv_mul_cancel_left] using hmul _ _ hi hf

end

section

/-! Gaussian covariance for every rational symplectic matrix. -/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

def HasGaussianFormula (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) : Prop :=
  ∃ (r : MpR) (c : C(PoissonAutomorphyNormalizationData.Domain ι, ℂ)),
    D.real.project r = PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) γ ∧
    (∀ Z, c Z ^ 2 = (PoissonAutomorphyNormalizationData.denominatorDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z)⁻¹) ∧
    ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      D.real.action r (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z) =
        (c (PoissonAutomorphyNormalizationData.ofSiegel Z) * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) Z z)⁻¹) •
          PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z)

theorem hasGaussianFormula_mul (γ δ : PoissonAutomorphyNormalizationData.Sp ι ℚ)
    (hγ : HasGaussianFormula D γ) (hδ : HasGaussianFormula D δ) :
    HasGaussianFormula D (γ * δ) := by
  obtain ⟨r, c, hr, hc, hact⟩ := hγ
  obtain ⟨s, d, hs, hd, hact'⟩ := hδ
  let e : C(PoissonAutomorphyNormalizationData.Domain ι, ℂ) :=
    ⟨fun Z => d Z * c (transformDomain (PoissonAutomorphyNormalizationData.realBlocks δ) Z),
      d.continuous.mul (c.continuous.comp (transformDomain_continuous _))⟩
  refine ⟨r * s, e, ?_, ?_, ?_⟩
  · rw [map_mul, hr, hs, map_mul]
  · intro Z
    change (d Z * c (transformDomain (PoissonAutomorphyNormalizationData.realBlocks δ) Z)) ^ 2 = _
    rw [mul_pow, hd, hc, realBlocks_mul]
    change ((PoissonAutomorphyNormalizationData.realBlocks δ).complexify.denominator Z.val).det⁻¹ *
      ((PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator ((PoissonAutomorphyNormalizationData.realBlocks δ).complexify.fractional Z.val)).det⁻¹ =
      ((composeBlocks (PoissonAutomorphyNormalizationData.realBlocks γ) (PoissonAutomorphyNormalizationData.realBlocks δ)).complexify.denominator Z.val).det⁻¹
    rw [complexify_composeBlocks, compose_denominator (PoissonAutomorphyNormalizationData.realBlocks γ).complexify
      (PoissonAutomorphyNormalizationData.realBlocks δ).complexify Z.val ((PoissonAutomorphyNormalizationData.realBlocks δ).denominator_det_isUnit (PoissonAutomorphyNormalizationData.toSiegel Z)),
      Matrix.det_mul, _root_.mul_inv_rev]
  · intro Z z
    rw [map_mul]
    change D.real.action r (D.real.action s (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z)) = _
    rw [hact', map_smul, hact, smul_smul, realBlocks_mul,
      compose_transformSiegel, compose_jacobiChange, compose_quadraticFactor]
    congr 1
    change (d (PoissonAutomorphyNormalizationData.ofSiegel Z) * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks δ) Z z)⁻¹) *
        (c (PoissonAutomorphyNormalizationData.ofSiegel ((PoissonAutomorphyNormalizationData.realBlocks δ).transformSiegel Z)) *
          (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) ((PoissonAutomorphyNormalizationData.realBlocks δ).transformSiegel Z) ((PoissonAutomorphyNormalizationData.realBlocks δ).jacobiChange Z z))⁻¹) =
      (d (PoissonAutomorphyNormalizationData.ofSiegel Z) * c (PoissonAutomorphyNormalizationData.ofSiegel ((PoissonAutomorphyNormalizationData.realBlocks δ).transformSiegel Z))) *
        (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks δ) Z z *
          PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) ((PoissonAutomorphyNormalizationData.realBlocks δ).transformSiegel Z) ((PoissonAutomorphyNormalizationData.realBlocks δ).jacobiChange Z z))⁻¹
    rw [_root_.mul_inv_rev]
    ring

theorem hasGaussianFormula_upper (B : Matrix ι ι ℚ) (hB : B.IsSymm) :
    HasGaussianFormula D (Generators.PoissonAutomorphyConstruction.upper B hB) := by
  let c := (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹
  refine ⟨D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.upper B hB), ContinuousMap.const _ c,
    D.normalizedRealLift_covers _, ?_, ?_⟩
  · intro Z
    change c ^ 2 = _
    rw [show c ^ 2 = _ from inv_pow (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι))) 2,
      PoissonAutomorphyNormalizationData.halfDet_sq]
    simp only [PoissonAutomorphyNormalizationData.denominatorDet, upper_denominator, Matrix.det_one]
  · intro Z z
    have hq : PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.upper B hB)) Z z = 1 := by
      rw [PoissonAutomorphyNormalizationData.quadraticFactor, correction_of_C_zero _ (upper_complex_blocks B hB).2.2.1, Complex.exp_zero]
    rw [hq, inv_one, mul_one]
    exact realAction_upper_gaussian D B hB Z z

theorem hasGaussianFormula_levi (A : (Matrix ι ι ℚ)ˣ) : HasGaussianFormula D (Generators.PoissonAutomorphyConstruction.levi A) := by
  let c := (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹
  refine ⟨D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.levi A), ContinuousMap.const _ c,
    D.normalizedRealLift_covers _, ?_, ?_⟩
  · intro Z
    change c ^ 2 = _
    rw [show c ^ 2 = _ from inv_pow (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι))) 2,
      PoissonAutomorphyNormalizationData.halfDet_sq]
    simp only [PoissonAutomorphyNormalizationData.denominatorDet, levi_denominator]
  · intro Z z
    have hq : PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.levi A)) Z z = 1 := by
      rw [PoissonAutomorphyNormalizationData.quadraticFactor, correction_of_C_zero _ (levi_complex_blocks A).2.2.1, Complex.exp_zero]
    rw [hq, inv_one, mul_one]
    exact realAction_levi_gaussian D A Z z

theorem hasGaussianFormula_weyl : HasGaussianFormula D (Generators.PoissonAutomorphyConstruction.weyl ι) := by
  let c : C(PoissonAutomorphyNormalizationData.Domain ι, ℂ) :=
    ⟨fun Z => (PoissonAutomorphyNormalizationData.halfDetDomain (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z)⁻¹,
      (PoissonAutomorphyNormalizationData.halfDetDomain_continuous _).inv₀ (fun Z => PoissonAutomorphyNormalizationData.halfDet_ne_zero _ (PoissonAutomorphyNormalizationData.toSiegel Z))⟩
  refine ⟨D.normalizedRealLift (Generators.PoissonAutomorphyConstruction.weyl ι), c, D.normalizedRealLift_covers _, ?_, ?_⟩
  · intro Z
    change (PoissonAutomorphyNormalizationData.halfDetDomain (PoissonAutomorphyNormalizationData.realBlocks (Generators.PoissonAutomorphyConstruction.weyl ι)) Z)⁻¹ ^ 2 = _
    rw [inv_pow, PoissonAutomorphyNormalizationData.halfDetDomain_sq]
  · intro Z z
    exact realAction_weyl_gaussian D Z z

theorem hasGaussianFormula (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) : HasGaussianFormula D γ :=
  rational_generator_induction (HasGaussianFormula D) (hasGaussianFormula_mul D)
    (hasGaussianFormula_upper D) (hasGaussianFormula_levi D) (hasGaussianFormula_weyl D) γ

end

section

/-! Identification of the coefficient with the prescribed determinant branch. -/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem realAction_same_projection (r s : MpR) (hproj : D.real.project r = D.real.project s) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : PoissonAutomorphyNormalizationData.realSchwartz ι, D.real.action r f = ε • D.real.action s f := by
  have hker : D.real.project (r * s⁻¹) = 1 := by
    rw [map_mul, map_inv, hproj, mul_inv_cancel]
  rcases (D.real.kernel _).mp hker with h | h
  · have heq : r = s := mul_inv_eq_one.mp h
    refine ⟨1, by norm_num, fun f => ?_⟩
    rw [heq, one_smul]
  · have heq : r = D.real.negOne * s := mul_inv_eq_iff_eq_mul.mp h
    refine ⟨-1, by norm_num, fun f => ?_⟩
    rw [heq, map_mul]
    change D.real.action D.real.negOne (D.real.action s f) = (-1 : ℂ) • D.real.action s f
    rw [D.real.genuine]
    apply Subtype.ext
    funext x
    change -((D.real.action s f).val x) = (-1 : ℂ) * (D.real.action s f).val x
    ring

omit [DecidableEq ι] in
theorem gaussianFunction_zero (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z 0 = 1 := by
  simp [PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent]

theorem gaussianTest_base : PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)) 0 = D.vacuum := by
  apply Subtype.ext
  funext x
  rw [PoissonAutomorphyGaussianPoisson.Construction.gaussianTest_apply, gaussianFunction_base, D.vacuum_eq]

theorem normalizedGaussianCoefficient (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) (c : C(PoissonAutomorphyNormalizationData.Domain ι, ℂ))
    (hc : ∀ Z, c Z ^ 2 = (PoissonAutomorphyNormalizationData.denominatorDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z)⁻¹)
    (hact : ∀ (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      D.real.action (D.normalizedRealLift γ) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z) =
        (c (PoissonAutomorphyNormalizationData.ofSiegel Z) * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) Z z)⁻¹) •
          PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z)) :
    ∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι, c (PoissonAutomorphyNormalizationData.ofSiegel Z) = (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z)⁻¹ := by
  have hne (Z : PoissonAutomorphyNormalizationData.Domain ι) : c Z ≠ 0 := by
    intro hz
    have h := hc Z
    rw [hz, zero_pow (by decide)] at h
    exact (inv_ne_zero (PoissonAutomorphyNormalizationData.denominatorDet_ne_zero _ _)) h.symm
  have hbase : c (PoissonAutomorphyNormalizationData.basePeriod ι) = (PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))⁻¹ := by
    have h := congrArg (fun f : PoissonAutomorphyNormalizationData.realSchwartz ι => f.val 0) (hact (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)) 0)
    rw [gaussianTest_base] at h
    change (D.real.action (D.normalizedRealLift γ) D.vacuum).val 0 =
      (c (PoissonAutomorphyNormalizationData.basePeriod ι) * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)) 0)⁻¹) *
        PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)))
          ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange (PoissonAutomorphyNormalizationData.toSiegel (PoissonAutomorphyNormalizationData.basePeriod ι)) 0) 0 at h
    rw [D.normalizedRealLift_coefficient, PoissonAutomorphyNormalizationData.quadraticFactor_zero, inv_one, mul_one,
      gaussianFunction_zero, mul_one] at h
    exact h.symm
  let f : C(PoissonAutomorphyNormalizationData.Domain ι, ℂ) := ⟨fun Z => (c Z)⁻¹, c.continuous.inv₀ hne⟩
  have hf := PoissonAutomorphyNormalizationData.halfDetDomain_unique (PoissonAutomorphyNormalizationData.realBlocks γ) f (fun Z => ?_) (by
    change (c (PoissonAutomorphyNormalizationData.basePeriod ι))⁻¹ = _
    rw [hbase, inv_inv]
    rfl)
  · intro Z
    have h := hf (PoissonAutomorphyNormalizationData.ofSiegel Z)
    change (c (PoissonAutomorphyNormalizationData.ofSiegel Z))⁻¹ = PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z at h
    rw [← h, inv_inv]
  · change (c Z)⁻¹ ^ 2 = _
    rw [inv_pow, hc, inv_inv]

theorem realAction_gaussian (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    D.real.action (D.normalizedRealLift γ) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z) =
      ((PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z)⁻¹ * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) Z z)⁻¹) •
        PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) := by
  obtain ⟨r, c, hr, hc, hact⟩ := hasGaussianFormula D γ
  obtain ⟨ε, hε, hεact⟩ := realAction_same_projection D (D.normalizedRealLift γ) r
    ((D.normalizedRealLift_covers γ).trans hr.symm)
  let e : C(PoissonAutomorphyNormalizationData.Domain ι, ℂ) := ⟨fun W => ε * c W, continuous_const.mul c.continuous⟩
  have he (W : PoissonAutomorphyNormalizationData.Domain ι) : e W ^ 2 = (PoissonAutomorphyNormalizationData.denominatorDet (PoissonAutomorphyNormalizationData.realBlocks γ) W)⁻¹ := by
    change (ε * c W) ^ 2 = _
    rw [mul_pow, hε, one_mul, hc]
  have heact (W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (w : ι → ℂ) :
      D.real.action (D.normalizedRealLift γ) (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D W w) =
        (e (PoissonAutomorphyNormalizationData.ofSiegel W) * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) W w)⁻¹) •
          PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel W) ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange W w) := by
    rw [hεact, hact, smul_smul]
    change (ε * (c (PoissonAutomorphyNormalizationData.ofSiegel W) * _)) • _ = ((ε * c (PoissonAutomorphyNormalizationData.ofSiegel W)) * _) • _
    rw [mul_assoc]
  rw [heact, normalizedGaussianCoefficient D γ e he heact]

end

/-! The theta transformation law from Poisson summation and Gaussian covariance. -/

variable {ι : Type*} [Fintype ι]

theorem thetaFunctional_tensor_smul (c : ℂ) (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    PoissonAutomorphyNormalizationData.thetaFunctional (PoissonAutomorphyNormalizationData.tensor (c • f) φ) = c * PoissonAutomorphyNormalizationData.thetaFunctional (PoissonAutomorphyNormalizationData.tensor f φ) := by
  change Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (CosetTests.PoissonAutomorphyConstruction.tensorRight φ (c • f)) = c • Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (CosetTests.PoissonAutomorphyConstruction.tensorRight φ f)
  rw [map_smul, map_smul]

variable [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem gaussian_theta_transformation (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    PoissonAutomorphyNormalizationData.theta (D.finiteAction γ φ) ((PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) =
      PoissonAutomorphyNormalizationData.halfDet (PoissonAutomorphyNormalizationData.realBlocks γ) Z * (PoissonAutomorphyNormalizationData.quadraticFactor (PoissonAutomorphyNormalizationData.realBlocks γ) Z z * PoissonAutomorphyNormalizationData.theta φ Z z) := by
  have h := PoissonAutomorphyGaussianPoisson.Construction.rational_theta_invariant D γ (PoissonAutomorphyNormalizationData.tensor (PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D Z z) φ)
  rw [D.rationalAction_tensor, realAction_gaussian, thetaFunctional_tensor_smul,
    PoissonAutomorphyGaussianPoisson.Construction.thetaFunctional_gaussian_tensor, PoissonAutomorphyGaussianPoisson.Construction.thetaFunctional_gaussian_tensor] at h
  apply mul_left_cancel₀
    (mul_ne_zero (inv_ne_zero (PoissonAutomorphyNormalizationData.halfDet_ne_zero (PoissonAutomorphyNormalizationData.realBlocks γ) Z))
      (inv_ne_zero (PoissonAutomorphyNormalizationData.quadraticFactor_ne_zero (PoissonAutomorphyNormalizationData.realBlocks γ) Z z)))
  rw [h]
  field_simp [PoissonAutomorphyNormalizationData.halfDet_ne_zero (PoissonAutomorphyNormalizationData.realBlocks γ) Z, PoissonAutomorphyNormalizationData.quadraticFactor_ne_zero (PoissonAutomorphyNormalizationData.realBlocks γ) Z z]

end RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction

namespace RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-!
# PoissonAutomorphy: Poisson summation and rational theta automorphy

All five conclusions follow for the supplied normalized Weil data. The helpers
prove absolute convergence, adelic Poisson summation, rational invariance, and
the Gaussian transformation with the prescribed continuous determinant branch.
The fixed specification is not imported. The audit covers the theorem and every
PoissonAutomorphy construction and helper declaration, allowing only Lean's classical foundations.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

theorem poisson_summation_and_rational_theta_automorphy
    (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    let g := PoissonAutomorphyNormalizationData.realBlocks γ
    (∀ f : PoissonAutomorphyNormalizationData.adelicSchwartz ι,
      Summable (fun x : ι → ℚ => ‖f.val (PoissonAutomorphyNormalizationData.diagonal x)‖)) ∧
    (∀ f : PoissonAutomorphyNormalizationData.adelicSchwartz ι,
      PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction γ f) = PoissonAutomorphyNormalizationData.thetaFunctional f) ∧
    (∀ (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Summable (fun x : ι → ℚ => ‖PoissonAutomorphyNormalizationData.thetaTerm φ Z z x‖)) ∧
    (∀ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι,
      PoissonAutomorphyNormalizationData.halfDet g Z ^ 2 = (g.complexify.denominator Z.matrix).det) ∧
    (∀ (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      PoissonAutomorphyNormalizationData.theta (D.finiteAction γ φ) (g.transformSiegel Z) (g.jacobiChange Z z) =
        PoissonAutomorphyNormalizationData.halfDet g Z * (PoissonAutomorphyNormalizationData.quadraticFactor g Z z * PoissonAutomorphyNormalizationData.theta φ Z z)) := by
  exact ⟨Convergence.PoissonAutomorphyConstruction.adelic_rational_norm_summable, PoissonAutomorphyGaussianPoisson.Construction.rational_theta_invariant D γ,
    Convergence.PoissonAutomorphyConstruction.gaussian_rational_norm_summable, PoissonAutomorphyNormalizationData.halfDet_sq (PoissonAutomorphyNormalizationData.realBlocks γ), Construction.gaussian_theta_transformation D γ⟩

end RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

end

end OAI
