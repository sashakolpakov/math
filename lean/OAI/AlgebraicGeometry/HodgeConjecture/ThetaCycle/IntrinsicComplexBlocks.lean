import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicBlock
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPeriodBlocks

/-! # Intrinsic Complex Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicComplexBlocks.CM

noncomputable section

/-! Complexified trace-coordinate block identities and the actual
geometric period graph, ready for local period covariance. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

theorem native_place_matrix_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R) :
    (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A M).map f = IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (M v).map f) := by
  apply Matrix.ext
  rintro ⟨v, a⟩ ⟨w, b⟩
  simp only [Matrix.map_apply, IntrinsicPlaceMatrices.CM.native_place_matrix_entry, apply_ite f, map_zero]

theorem native_place_matrix_add {R : Type*} [CommRing R]
    (M N : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R) :
    IntrinsicPlaceMatrices.CM.nativePlaceMatrix A M + IntrinsicPlaceMatrices.CM.nativePlaceMatrix A N = IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => M v + N v) := by
  unfold IntrinsicPlaceMatrices.CM.nativePlaceMatrix
  rw [← map_add, ← Matrix.blockDiagonal_add]
  rfl

theorem native_place_matrix_mul {R : Type*} [CommRing R]
    (M N : Fin A.places → Matrix (Fin (3 * m)) (Fin (3 * m)) R) :
    IntrinsicPlaceMatrices.CM.nativePlaceMatrix A M * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A N = IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => M v * N v) := by
  unfold IntrinsicPlaceMatrices.CM.nativePlaceMatrix
  rw [← map_mul, ← Matrix.blockDiagonal_mul]

def nativeComplexPosition : (Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ)ˣ :=
  Units.map Complex.ofRealHom.mapMatrix.toMonoidHom (IntrinsicPlaceMatrices.CM.nativePositionMatrix A)

def nativeComplexMomentum : (Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ)ˣ :=
  Units.map Complex.ofRealHom.mapMatrix.toMonoidHom (IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A)

theorem native_complex_momentum_position_dual :
    (nativeComplexMomentum A).val * (nativeComplexPosition A).val.transpose = 1 := by
  apply _root_.mul_eq_one_comm.mp
  have h := congrArg (fun M : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℝ => M.map Complex.ofRealHom)
    (IntrinsicPlaceMatrices.CM.native_position_momentum_matrix_dual A)
  simpa only [Matrix.map_mul, ← Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using! h

variable (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

theorem native_complex_block_intertwining (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) :
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.A * (nativeComplexMomentum A).val =
      (nativeComplexMomentum A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.A) ∧
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.B * (nativeComplexPosition A).val =
      (nativeComplexMomentum A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.B) ∧
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.C * (nativeComplexMomentum A).val =
      (nativeComplexPosition A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.C) ∧
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).complexify.D * (nativeComplexPosition A).val =
      (nativeComplexPosition A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (IntrinsicBlock.CM.nativeLocalSiegelBlocks A P g v).complexify.D) := by
  have h := IntrinsicBlock.CM.native_block_intertwining A P g
  let f := fun M : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℝ => M.map Complex.ofRealHom
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [f, Matrix.map_mul, native_place_matrix_map] using! congrArg f h.1
  · simpa only [f, Matrix.map_mul, native_place_matrix_map] using! congrArg f h.2.1
  · simpa only [f, Matrix.map_mul, native_place_matrix_map] using! congrArg f h.2.2.1
  · simpa only [f, Matrix.map_mul, native_place_matrix_map] using! congrArg f h.2.2.2

theorem native_period_graph_matrix (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix * (nativeComplexPosition A).val =
      (nativeComplexMomentum A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix) := by
  have h := IntrinsicPeriodBlocks.CM.native_period_block_matrix A P z
  change (nativeComplexPosition A).val.transpose * (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix *
    (nativeComplexPosition A).val = IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix) at h
  have he := congrArg (fun M => (nativeComplexMomentum A).val * M) h
  simpa only [← Matrix.mul_assoc, native_complex_momentum_position_dual, one_mul] using he

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicComplexBlocks.CM
