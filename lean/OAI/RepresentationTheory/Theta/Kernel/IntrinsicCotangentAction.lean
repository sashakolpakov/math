import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalActionParameter
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumCoordinates
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiBlockAction

/-! # Intrinsic Cotangent Action -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic

noncomputable section

/-! Full native Gaussian covariance recovers the actual SU action in
the cotangent coordinates determined by the native position map. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P}

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

def nativePhaseAction (g : Adelic.RationalSU.ArchimedeanSU F H) (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m) := fun v i =>
  A.real v (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl (A.enumerate v))
    (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))
      (fun j => (A.real v).symm (u v j)) i)

def cotangentCoordinates (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ :=
  Sum.elim (B.realPosition (fun v i => u v (.inl i)))
    (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun v i => u v (.inr i)))

theorem native_phase_jacobi (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates.phaseParameter (B.period (B.ball g • z)).matrix
      (B.realPosition (fun v i => nativePhaseAction (A := A) (P := P) g u v (.inl i)))
      (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun v i => nativePhaseAction (A := A) (P := P) g u v (.inr i))) =
      (B.symplectic g).jacobiChange (B.period z)
        (IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates.phaseParameter (B.period z).matrix (B.realPosition (fun v i => u v (.inl i)))
          (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun v i => u v (.inr i)))) := by
  apply IntrinsicMomentumCoordinates.Intrinsic.local_jacobi_joint_injective B
  funext v
  dsimp only
  rw [IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates.phaseParameter,IntrinsicLocalJacobiPhase.Intrinsic.local_phase_parameter B hO]
  have h := IntrinsicLocalActionParameter.Intrinsic.native_local_action_parameter B hO hψ g z v
    (fun i => u v (.inl i)) (fun i => u v (.inr i))
    (IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates.phaseParameter (B.period z).matrix (B.realPosition (fun w i => u w (.inl i)))
      (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun w i => u w (.inr i))))
    (IntrinsicLocalJacobiPhase.Intrinsic.local_phase_parameter B hO z v (fun w i => u w (.inl i)) (fun w i => u w (.inr i)))
  have hp := D.covers (.inl (A.enumerate v))
    (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v)))
  change Weil.AdelicSplitting.Oscillator.Construction.localProjection _ _ _
    (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl (A.enumerate v)) (g (A.enumerate v))) = _ at hp
  dsimp only at h
  rw [hp] at h
  have hu : Sum.elim (fun i => u v (.inl i)) (fun i => u v (.inr i)) =
      fun i => A.real v ((A.real v).symm (u v i)) := by
    funext i
    cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,RingEquiv.apply_symm_apply]
  rw [hu,Weil.Local.FieldFourier.Construction.fieldSymplecticMap_action] at h
  exact h

theorem native_cotangent_action (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (hG : Adelic.DataTheta.GeometryIdentification B) (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    (Adelic.DataTheta.blockMatrix (B.symplectic g)).mulVec (Adelic.DataTheta.swapPhase (cotangentCoordinates B u)) =
      Adelic.DataTheta.swapPhase (cotangentCoordinates B (nativePhaseAction (A := A) (P := P) g u)) := by
  let q := B.realPosition (fun v i => u v (.inl i))
  let p := IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun v i => u v (.inr i))
  have ht := IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates.phase_parameter_transform (B.symplectic g) (B.period z) q p
  have h := native_phase_jacobi B hO hψ g z u
  have hperiod := hG.2.2.2.2.2.2.2.2.2.2.1 g z
  rw [← hperiod] at ht
  obtain ⟨hq,hp⟩ := IntrinsicJacobiBlockAction.IntrinsicPhaseCoordinates.phase_parameter_injective (B.period (B.ball g • z)) _ _ _ _ (h.trans ht.symm)
  change B.realPosition (fun v i => nativePhaseAction (A := A) (P := P) g u v (.inl i)) =
    (B.symplectic g).D.mulVec q + (B.symplectic g).C.mulVec p at hq
  change IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun v i => nativePhaseAction (A := A) (P := P) g u v (.inr i)) =
    (B.symplectic g).B.mulVec q + (B.symplectic g).A.mulVec p at hp
  unfold Adelic.DataTheta.blockMatrix
  rw [Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i =>
    change ((B.symplectic g).A.mulVec p + (B.symplectic g).B.mulVec q) i = _
    rw [add_comm,← hp]
    rfl
  | inr i =>
    change ((B.symplectic g).C.mulVec p + (B.symplectic g).D.mulVec q) i = _
    rw [add_comm,← hq]
    rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic
