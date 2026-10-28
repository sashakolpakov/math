import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPlaceMatrices
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCovariance
import OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction

/-! # Intrinsic Block -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicBlock.CM

noncomputable section

section

/-! The real trace-coordinate phase map and the exact block action of
the native real-place symplectic matrices. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
open OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

def nativePhaseUnflatten (x : (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℝ) :
    Fin A.places → RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m) := fun v =>
  Sum.elim (IntrinsicPlaceMatrices.CM.nativePositionUnflatten A (fun i => x (.inl i)) v)
    (IntrinsicPlaceMatrices.CM.nativePositionUnflatten A (fun i => x (.inr i)) v)

theorem native_phase_unflatten_inl (x : (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℝ)
    (v : Fin A.places) (j : Fin (3 * m)) :
    nativePhaseUnflatten A x v (.inl j) = x (.inl (v, finProdFinEquiv.symm j)) := rfl

theorem native_phase_unflatten_inr (x : (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℝ)
    (v : Fin A.places) (j : Fin (3 * m)) :
    nativePhaseUnflatten A x v (.inr j) = x (.inr (v, finProdFinEquiv.symm j)) := rfl

theorem native_phase_matrix_coordinates (x : (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℝ) :
    RepresentationTheory.Theta.Adelic.PhaseCoordinates.realPhaseCoordinates A (nativePhaseUnflatten A x) =
      Sum.elim ((IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val.mulVec (fun i => x (.inl i)))
        ((IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val.mulVec (fun i => x (.inr i))) := by
  funext i
  cases i with
  | inl i => exact (congrFun (IntrinsicPlaceMatrices.CM.native_position_matrix_apply A (fun j => x (.inl j))) i).symm
  | inr i => exact (congrFun (IntrinsicPlaceMatrices.CM.native_momentum_matrix_apply A (fun j => x (.inr j))) i).symm

theorem native_phase_swapped_coordinates (q p : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) :
    RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (RepresentationTheory.Theta.Adelic.PhaseCoordinates.realPhaseCoordinates A (nativePhaseUnflatten A (Sum.elim q p))) =
      Sum.elim ((IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val.mulVec p) ((IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val.mulVec q) := by
  rw [native_phase_matrix_coordinates]
  rfl

variable (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

def nativeLocalSiegelBlocks (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin (3 * m)) ℝ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))

theorem native_phase_place_action (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (q p : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) :
    RepresentationTheory.Theta.Adelic.RealSymplecticAction.realNativeAction A P g (nativePhaseUnflatten A (Sum.elim q p)) =
      nativePhaseUnflatten A (Sum.elim
        ((IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).D)).mulVec q +
          (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).C)).mulVec p)
        ((IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).B)).mulVec q +
          (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).A)).mulVec p)) := by
  funext v i
  change RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v)
    (Sum.elim (IntrinsicPlaceMatrices.CM.nativePositionUnflatten A q v) (IntrinsicPlaceMatrices.CM.nativePositionUnflatten A p v)) i = _
  have h := RealGaussianCovariance.CM.swapped_symplectic_phase_action (OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.Adelic.RealSymplecticAction.localRealSymplectic A P g v))
    (IntrinsicPlaceMatrices.CM.nativePositionUnflatten A q v) (IntrinsicPlaceMatrices.CM.nativePositionUnflatten A p v)
  rw [OscillatorPhaseOrder.CM.swap_symplectic_phase_involutive] at h
  cases i with
  | inl j =>
    have hj := congrFun h (.inl j)
    simpa only [native_phase_unflatten_inl, Sum.elim_inl, Pi.add_apply,
      IntrinsicPlaceMatrices.CM.native_place_matrix_mulVec, Equiv.apply_symm_apply,
      RealGaussianCovariance.CM.transformedPositionShift, nativeLocalSiegelBlocks] using! hj
  | inr j =>
    have hj := congrFun h (.inr j)
    simpa only [native_phase_unflatten_inr, Sum.elim_inr, Pi.add_apply,
      IntrinsicPlaceMatrices.CM.native_place_matrix_mulVec, Equiv.apply_symm_apply,
      RealGaussianCovariance.CM.transformedMomentumShift, nativeLocalSiegelBlocks] using! hj

end

section

/-! The actual global symplectic action intertwines the local block
actions through the trace position and momentum matrices. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

theorem native_global_block_action (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) (q p : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) :
    (RepresentationTheory.Theta.Adelic.DataTheta.blockMatrix (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g)).mulVec
      (Sum.elim ((IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val.mulVec p) ((IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val.mulVec q)) =
    Sum.elim
      ((IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val.mulVec
        ((IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).B)).mulVec q +
          (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).A)).mulVec p))
      ((IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val.mulVec
        ((IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).D)).mulVec q +
          (IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).C)).mulVec p)) := by
  let x := nativePhaseUnflatten A (Sum.elim q p)
  have h := RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks_action A P g x
  have hn := funext (fun v => RepresentationTheory.Theta.Adelic.RealSymplecticAction.realNativeAction_apply A P g x v)
  rw [← hn] at h
  change (RepresentationTheory.Theta.Adelic.DataTheta.blockMatrix (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g)).mulVec
    (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (RepresentationTheory.Theta.Adelic.PhaseCoordinates.realPhaseCoordinates A
      (nativePhaseUnflatten A (Sum.elim q p)))) = _ at h
  rw [native_phase_swapped_coordinates, native_phase_place_action,
    native_phase_swapped_coordinates] at h
  exact h

end

/-! The four exact matrix identities behind the global/local real
symplectic action in trace position and momentum coordinates. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction

theorem block_action_intertwining_matrices
    {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (G : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I R) (S T A B C D : Matrix I I R)
    (hact : ∀ q p : I → R,
      (Matrix.fromBlocks G.A G.B G.C G.D).mulVec (Sum.elim (S.mulVec p) (T.mulVec q)) =
        Sum.elim (S.mulVec (B.mulVec q + A.mulVec p)) (T.mulVec (D.mulVec q + C.mulVec p))) :
    G.A * S = S * A ∧ G.B * T = S * B ∧ G.C * S = T * C ∧ G.D * T = T * D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply Matrix.ext; intro i j
  · have h := congrFun (hact 0 (Pi.single j 1)) (.inl i)
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.mul_apply, Pi.single_apply] using h
  · have h := congrFun (hact (Pi.single j 1) 0) (.inl i)
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.mul_apply, Pi.single_apply] using h
  · have h := congrFun (hact 0 (Pi.single j 1)) (.inr i)
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.mul_apply, Pi.single_apply] using h
  · have h := congrFun (hact (Pi.single j 1) 0) (.inr i)
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.mul_apply, Pi.single_apply] using h

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)

theorem native_block_intertwining (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) :
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).A * (IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val =
      (IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).A) ∧
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).B * (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val =
      (IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).B) ∧
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).C * (IntrinsicPlaceMatrices.CM.nativeMomentumMatrix A).val =
      (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).C) ∧
    (RepresentationTheory.Theta.Adelic.RealSymplecticAction.realSymplecticBlocks A P g).D * (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val =
      (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val * IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (nativeLocalSiegelBlocks A P g v).D) :=
  block_action_intertwining_matrices _ _ _ _ _ _ _ (native_global_block_action A P g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicBlock.CM
