import OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase
import OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction

/-! # Complex Intrinsic Action -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.IntrinsicPhaseIntertwining

/-! The native real tensor frame intertwines the actual unitary action
with the constructed real symplectic-coordinate action. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

theorem frame_action {k : Type} [Field k] {d : k} {n m : ℕ}
    {H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)}
    {K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)}
    (c : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K) (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) (s : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K c g) (c.coordinates s) =
      c.coordinates (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g s) := by
  change Matrix.toLin' (LinearMap.toMatrix' (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H K c g).toLinearMap) (c.coordinates s) = _
  rw [Matrix.toLin'_toMatrix']
  change c.coordinates (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g (c.coordinates.symm (c.coordinates s))) = _
  rw [LinearEquiv.symm_apply_apply]

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem nativeRealPhase_apply
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P s = PhaseCoordinates.realPhaseCoordinates A (fun v j => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) j)) := rfl

theorem realCoordinateAction_nativePhase (g : RationalSU.ArchimedeanSU F H)
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    RealSymplecticAction.realCoordinateAction A P g (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P s) =
      IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P (IntrinsicGeometricAction.Intrinsic.nativeTensorAction A g s) := by
  rw [nativeRealPhase_apply, nativeRealPhase_apply, RealSymplecticAction.realCoordinateAction_native]
  apply congrArg (PhaseCoordinates.realPhaseCoordinates A)
  funext v
  rw [RealSymplecticAction.realNativeAction_apply]
  have he : (fun j => (A.real v).symm (A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) j))) =
        (P.localFrame (.inl (A.enumerate v))).coordinates (s v) := by
    funext j
    exact (A.real v).symm_apply_apply _
  rw [he]
  exact congrArg (fun t => fun i => A.real v (t i))
    (frame_action (P.localFrame (.inl (A.enumerate v)))
      (FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))) (s v))

end RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.IntrinsicPhaseIntertwining

namespace RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate

/-! The complexification of the actual real symplectic action is the
geometric standard/dual tensor action in the constructed coordinates. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.IntrinsicPhaseIntertwining
open OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction

def complexifiedLinear {I : Type*} [Fintype I] [DecidableEq I]
    (e : (I → ℝ) →ₗ[ℝ] (I → ℝ)) : (I → ℂ) →ₗ[ℂ] (I → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix' e).map Complex.ofRealHom)

theorem complexifiedLinear_real {I : Type*} [Fintype I] [DecidableEq I]
    (e : (I → ℝ) →ₗ[ℝ] (I → ℝ)) (x : I → ℝ) :
    complexifiedLinear e (fun i => (x i : ℂ)) = fun i => (e x i : ℂ) := by
  funext i
  exact (Complex.ofRealHom.map_mulVec (LinearMap.toMatrix' e) x i).symm.trans
    (congrArg (fun r : ℝ => (r : ℂ)) (congrFun (LinearMap.toMatrix'_mulVec e x) i))

theorem complexLinear_ext_real {I V : Type*} [Fintype I] [AddCommGroup V] [Module ℂ V]
    (f g : (I → ℂ) →ₗ[ℂ] V)
    (hr : ∀ x : I → ℝ, f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) : f = g := by
  apply (Pi.basisFun ℂ I).ext
  intro i
  rw [BilinearCoordinates.complex_basis_real]
  exact hr _

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem complex_coordinate_action (g : RationalSU.ArchimedeanSU F H)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :
    ComplexPhaseCoordinates.complexPhaseCoordinates A P (complexifiedLinear (RealSymplecticAction.realCoordinateAction A P g).toLinearMap x) =
      BallGeometryData.geometricAction A g (ComplexPhaseCoordinates.complexPhaseCoordinates A P x) := by
  have hlinear : (ComplexPhaseCoordinates.complexPhaseCoordinates A P).toLinearEquiv.toLinearMap.comp
      (complexifiedLinear (RealSymplecticAction.realCoordinateAction A P g).toLinearMap) =
      (TensorGeometricAction.geometricActionLinear A g).comp (ComplexPhaseCoordinates.complexPhaseCoordinates A P).toLinearEquiv.toLinearMap := by
    apply complexLinear_ext_real
    intro u
    obtain ⟨s, rfl⟩ := (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P).surjective u
    rw [LinearMap.comp_apply, LinearMap.comp_apply, complexifiedLinear_real]
    have hs : ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun i => (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P s i : ℂ)) =
        BallGeometryData.realTensorComponents A s := ComplexPhaseCoordinates.complexPhaseCoordinates_native A P s
    have ht : ComplexPhaseCoordinates.complexPhaseCoordinates A P
        (fun i => (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P (IntrinsicGeometricAction.Intrinsic.nativeTensorAction A g s) i : ℂ)) =
        BallGeometryData.realTensorComponents A (IntrinsicGeometricAction.Intrinsic.nativeTensorAction A g s) :=
      ComplexPhaseCoordinates.complexPhaseCoordinates_native A P (IntrinsicGeometricAction.Intrinsic.nativeTensorAction A g s)
    have he : (RealSymplecticAction.realCoordinateAction A P g).toLinearMap (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P s) =
        IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P (IntrinsicGeometricAction.Intrinsic.nativeTensorAction A g s) :=
      IntrinsicPhaseIntertwining.realCoordinateAction_nativePhase A P g s
    rw [he]
    change ComplexPhaseCoordinates.complexPhaseCoordinates A P _ = TensorGeometricAction.geometricActionLinear A g (ComplexPhaseCoordinates.complexPhaseCoordinates A P _)
    rw [hs, ht, TensorGeometricAction.geometricActionLinear_apply]
    exact (IntrinsicGeometricAction.Intrinsic.native_geometric_action A g s).symm
  exact (LinearMap.congr_fun hlinear x).trans (TensorGeometricAction.geometricActionLinear_apply A g _)

end RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate

namespace RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Siegel

/-! Complexification commutes with the explicit phase swap. Thus the
constructed Siegel blocks act on the actual complex geometric coordinates. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction

theorem swap_cast {I : Type} (x : (I ⊕ I) → ℝ) :
    DataTheta.swapPhase (fun i => (x i : ℂ)) = fun i => ((DataTheta.swapPhase x i : ℝ) : ℂ) := by
  funext i
  cases i <;> rfl

theorem swap_swap {I k : Type} (x : (I ⊕ I) → k) :
    DataTheta.swapPhase (DataTheta.swapPhase x) = x := by
  funext i
  cases i <;> rfl

theorem complexified_swap {I : Type} [Fintype I] [DecidableEq I]
    (e : ((I ⊕ I) → ℝ) ≃ₗ[ℝ] ((I ⊕ I) → ℝ)) (x : (I ⊕ I) → ℂ) :
    Coordinate.complexifiedLinear (BilinearCoordinates.Symplectic.swapConjugate e).toLinearMap (DataTheta.swapPhase x) =
      DataTheta.swapPhase (Coordinate.complexifiedLinear e.toLinearMap x) := by
  have h : (Coordinate.complexifiedLinear (BilinearCoordinates.Symplectic.swapConjugate e).toLinearMap).comp
      (BilinearCoordinates.Symplectic.phaseSwapLinear (k := ℂ)).toLinearMap =
      (BilinearCoordinates.Symplectic.phaseSwapLinear (k := ℂ)).toLinearMap.comp (Coordinate.complexifiedLinear e.toLinearMap) := by
    apply Coordinate.complexLinear_ext_real
    intro u
    change Coordinate.complexifiedLinear (BilinearCoordinates.Symplectic.swapConjugate e).toLinearMap
      (DataTheta.swapPhase (fun i => (u i : ℂ))) = DataTheta.swapPhase (Coordinate.complexifiedLinear e.toLinearMap _)
    rw [swap_cast, Coordinate.complexifiedLinear_real, Coordinate.complexifiedLinear_real, swap_cast]
    change (fun i => (BilinearCoordinates.Symplectic.swapConjugate e (DataTheta.swapPhase u) i : ℂ)) = _
    rw [BilinearCoordinates.Symplectic.swapConjugate_apply, swap_swap]
    rfl
  exact LinearMap.congr_fun h x

theorem complexify_blockMatrix {I : Type} [Fintype I] [DecidableEq I]
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ) :
    DataTheta.blockMatrix g.complexify = (DataTheta.blockMatrix g).map Complex.ofRealHom := by
  ext i j
  cases i <;> cases j <;> rfl

theorem complexified_blocks_swap {I : Type} [Fintype I] [DecidableEq I]
    (e : ((I ⊕ I) → ℝ) ≃ₗ[ℝ] ((I ⊕ I) → ℝ))
    (hp : ∀ x y, DataTheta.standardPairing (e x) (e y) = DataTheta.standardPairing x y)
    (x : (I ⊕ I) → ℂ) :
    (DataTheta.blockMatrix (PoissonAutomorphyNormalizationData.blocks
      (BilinearCoordinates.Symplectic.linearSymplectic (BilinearCoordinates.Symplectic.swapConjugate e) (BilinearCoordinates.Symplectic.swapConjugate_preserves e hp))).complexify).mulVec
        (DataTheta.swapPhase x) = DataTheta.swapPhase (Coordinate.complexifiedLinear e.toLinearMap x) := by
  rw [complexify_blockMatrix, BilinearCoordinates.Symplectic.blocks_matrix]
  exact complexified_swap e x

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem complex_siegel_action (g : RationalSU.ArchimedeanSU F H)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :
    (DataTheta.blockMatrix (RealSymplecticAction.realSymplecticBlocks A P g).complexify).mulVec (DataTheta.swapPhase x) =
      DataTheta.swapPhase (Coordinate.complexifiedLinear (RealSymplecticAction.realCoordinateAction A P g).toLinearMap x) := by
  exact complexified_blocks_swap (RealSymplecticAction.realCoordinateAction A P g)
    (RealSymplecticAction.realCoordinateAction_preserves A P g) x

end RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Siegel

end

end OAI
