import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicComplexBlocks
import OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction

/-! # Intrinsic Jacobi -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicJacobi.CM

noncomputable section

section

/-! Exact local period covariance and the product formula for the
global Siegel denominator, derived from the geometric period graph. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

def nativeDenominatorBlock (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ :=
  IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.denominator
    (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix)

def nativeNumeratorBlock (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ :=
  IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.numerator
    (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix)

theorem native_denominator_block_intertwining (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix *
      (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val = (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val * nativeDenominatorBlock A P g z := by
  have h := IntrinsicComplexBlocks.CM.native_complex_block_intertwining A P g
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, Matrix.add_mul, Matrix.mul_assoc, IntrinsicComplexBlocks.CM.native_period_graph_matrix,
    ← Matrix.mul_assoc, h.2.2.1, h.2.2.2, Matrix.mul_assoc, ← Matrix.mul_add,
    IntrinsicComplexBlocks.CM.native_place_matrix_mul, IntrinsicComplexBlocks.CM.native_place_matrix_add]
  rfl

theorem native_numerator_block_intertwining (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.numerator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix *
      (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val = (IntrinsicComplexBlocks.CM.nativeComplexMomentum A).val * nativeNumeratorBlock A P g z := by
  have h := IntrinsicComplexBlocks.CM.native_complex_block_intertwining A P g
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator, Matrix.add_mul, Matrix.mul_assoc, IntrinsicComplexBlocks.CM.native_period_graph_matrix,
    ← Matrix.mul_assoc, h.1, h.2.1, Matrix.mul_assoc, ← Matrix.mul_add,
    IntrinsicComplexBlocks.CM.native_place_matrix_mul, IntrinsicComplexBlocks.CM.native_place_matrix_add]
  rfl

theorem native_period_blocks_fractional (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix) *
      nativeDenominatorBlock A P g z = nativeNumeratorBlock A P g z := by
  have hf : (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix *
      (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix =
      (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.numerator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix := by
    rw [RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance.geometric_period_covariance]
    exact (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.fractional_mul_denominator _
      ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).denominator_det_isUnit (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z))
  have h := congrArg (fun M => M * (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val) hf
  rw [Matrix.mul_assoc, native_denominator_block_intertwining, ← Matrix.mul_assoc,
    IntrinsicComplexBlocks.CM.native_period_graph_matrix, native_numerator_block_intertwining] at h
  have he := congrArg (fun M => (IntrinsicComplexBlocks.CM.nativeComplexMomentum A).inv * M) h
  simpa only [← Matrix.mul_assoc, (IntrinsicComplexBlocks.CM.nativeComplexMomentum A).inv_val, one_mul] using he

theorem native_local_period_covariance (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z) =
      (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).transformSiegel (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z) := by
  have h := native_period_blocks_fractional A P g z
  unfold nativeDenominatorBlock nativeNumeratorBlock at h
  rw [IntrinsicComplexBlocks.CM.native_place_matrix_mul] at h
  have hv : (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix *
      (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.denominator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix =
      (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.numerator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix := by
    apply Matrix.ext
    intro i j
    have he := congrArg (fun M : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ =>
      M (v, finProdFinEquiv.symm i) (v, finProdFinEquiv.symm j)) h
    simpa only [IntrinsicPlaceMatrices.CM.native_place_matrix_entry, ite_true, Equiv.apply_symm_apply] using he
  apply RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance.siegel_matrix_ext
  change (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v (RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom A g • z)).matrix =
    (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.numerator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix *
      ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.denominator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix)⁻¹
  rw [← hv, Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).denominator_det_isUnit (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)), Matrix.mul_one]

theorem native_global_denominator_det_product (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix).det =
      ∏ v, ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.denominator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix).det := by
  have h := congrArg Matrix.det (native_denominator_block_intertwining A P g z)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hT : (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.det ≠ 0 :=
    (Matrix.GeneralLinearGroup.det (IntrinsicComplexBlocks.CM.nativeComplexPosition A)).ne_zero
  apply mul_right_cancel₀ hT
  rw [h, mul_comm]
  congr 1
  exact IntrinsicPlaceMatrices.CM.native_place_matrix_det A _

end

section

/-! Inverse denominators and quadratic correction matrices in the
actual native position coordinates. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

theorem native_place_matrix_one {R : Type*} [CommRing R] :
    IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun _ => (1 : Matrix (Fin (3 * m)) (Fin (3 * m)) R)) = 1 := by
  unfold IntrinsicPlaceMatrices.CM.nativePlaceMatrix
  change Matrix.reindexRingEquiv R (IntrinsicPlaceMatrices.CM.nativePlaceIndexEquiv A)
    (Matrix.blockDiagonal (1 : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R)) = 1
  rw [Matrix.blockDiagonal_one, map_one]

theorem native_place_matrix_transpose {R : Type*} [CommRing R]
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R) :
    (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A M).transpose = IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (M v).transpose) := by
  apply Matrix.ext
  rintro ⟨v, a⟩ ⟨w, b⟩
  simp only [Matrix.transpose_apply, IntrinsicPlaceMatrices.CM.native_place_matrix_entry]
  by_cases h : v = w
  · subst w
    simp only [ite_true]
  · simp only [h, Ne.symm h, ite_false]

theorem native_place_matrix_inv
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) ℂ)
    (hM : ∀ v, IsUnit (M v).det) :
    (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A M)⁻¹ = IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (M v)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [IntrinsicComplexBlocks.CM.native_place_matrix_mul]
  simp only [Matrix.mul_nonsing_inv _ (hM _)]
  exact native_place_matrix_one A

variable (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

theorem native_denominator_block_det_isUnit (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    IsUnit (nativeDenominatorBlock A P g z).det := by
  rw [nativeDenominatorBlock, IntrinsicPlaceMatrices.CM.native_place_matrix_det]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun v _ =>
    ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).denominator_det_isUnit (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)).ne_zero))

theorem native_inverse_denominator_intertwining (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix)⁻¹ *
      (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val = (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val * (nativeDenominatorBlock A P g z)⁻¹ := by
  have h := congrArg (fun M =>
    ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix)⁻¹ * M *
      (nativeDenominatorBlock A P g z)⁻¹) (native_denominator_block_intertwining A P g z)
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).denominator_det_isUnit (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z)), one_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    (native_denominator_block_det_isUnit A P g z), Matrix.mul_one] at h
  exact h.symm

theorem native_jacobi_matrix_intertwining (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.transpose *
      ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix)⁻¹.transpose =
    IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v =>
      ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.denominator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix)⁻¹.transpose) *
      (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.transpose := by
  have h := congrArg Matrix.transpose (native_inverse_denominator_intertwining A P g z)
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h
  rw [h, nativeDenominatorBlock, native_place_matrix_inv A _ (fun v =>
    (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).denominator_det_isUnit (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)),
    native_place_matrix_transpose]

theorem native_correction_matrix (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix)⁻¹ *
      (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.C =
    (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v =>
      ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.denominator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix)⁻¹ *
        (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.C) * (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.transpose := by
  have hC := (IntrinsicComplexBlocks.CM.native_complex_block_intertwining A P g).2.2.1
  have h := congrArg (fun M => M * (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.transpose) hC
  rw [Matrix.mul_assoc, IntrinsicComplexBlocks.CM.native_complex_momentum_position_dual, Matrix.mul_one] at h
  rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, native_inverse_denominator_intertwining,
    Matrix.mul_assoc (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val, nativeDenominatorBlock,
    native_place_matrix_inv A _ (fun v =>
      (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).denominator_det_isUnit (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)),
    IntrinsicComplexBlocks.CM.native_place_matrix_mul]

end

/-! The literal local Jacobi parameters and quadratic corrections
recover the global ones in the trace-normalized coordinates. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

theorem native_position_matrix_column (v : Fin A.places) (a : Fin 3 × Fin m) (i : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) :
    (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val i (v, a) = RepresentationTheory.Theta.Adelic.LocalPositionInclusion.realPositionColumn A v i (finProdFinEquiv a) := by
  have h := congrFun (IntrinsicPeriodBlocks.CM.native_position_matrix_single A v a) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem native_local_jacobi_parameter (v : Fin A.places) (a : Fin 3 × Fin m) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.transpose.mulVec ξ (v, a) =
      RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ (finProdFinEquiv a) := by
  change (∑ i, ((IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val i (v, a) : ℂ) * ξ i) =
    ∑ i, (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.realPositionColumn A v i (finProdFinEquiv a) : ℂ) * ξ i
  simp only [native_position_matrix_column]

theorem native_local_jacobi_parameter_function (v : Fin A.places) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (fun j => (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.transpose.mulVec ξ (v, finProdFinEquiv.symm j)) =
      RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ := by
  funext j
  simp only [native_local_jacobi_parameter, Equiv.apply_symm_apply]

theorem native_place_matrix_pairing
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) ℂ)
    (x y : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    x ⬝ᵥ (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A M).mulVec y =
      ∑ v, (fun j => x (v, finProdFinEquiv.symm j)) ⬝ᵥ
        (M v).mulVec (fun j => y (v, finProdFinEquiv.symm j)) := by
  change (∑ i, x i * (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A M).mulVec y i) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  simp only [IntrinsicPlaceMatrices.CM.native_place_matrix_mulVec]
  simpa only [Equiv.symm_apply_apply, dotProduct] using Equiv.sum_comp finProdFinEquiv (fun j => x (v, finProdFinEquiv.symm j) *
    (M v).mulVec (fun j => y (v, finProdFinEquiv.symm j)) j)

variable (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

theorem native_local_jacobi_covariance (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places)
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ((RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).jacobiChange (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ) =
      (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).jacobiChange (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)
        (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ) := by
  funext j
  have h := congrArg (fun M : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ =>
    M.mulVec ξ (v, finProdFinEquiv.symm j)) (native_jacobi_matrix_intertwining A P g z)
  simp only [← Matrix.mulVec_mulVec, native_local_jacobi_parameter,
    Equiv.apply_symm_apply, IntrinsicPlaceMatrices.CM.native_place_matrix_mulVec] at h
  exact h

theorem native_theta_correction_sum (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).thetaCorrectionForm (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z) ξ ξ =
      ∑ v, (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).thetaCorrectionForm (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z)
        (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ) (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localJacobiParameter A v ξ) := by
  simp only [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply, ← Finset.mul_sum]
  congr 1
  rw [native_correction_matrix]
  have hp := ComplexMultiplication.SymplecticThetaCompletion.CM.bilinear_matrix_pullback (IntrinsicComplexBlocks.CM.nativeComplexPosition A).val.transpose
    (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v =>
      ((IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.denominator (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix)⁻¹ *
        (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.C)) ξ
  simp only [Matrix.transpose_transpose] at hp
  rw [← hp, native_place_matrix_pairing]
  simp only [native_local_jacobi_parameter_function]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicJacobi.CM
