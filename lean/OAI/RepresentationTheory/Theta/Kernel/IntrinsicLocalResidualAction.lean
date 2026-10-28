import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionFixedShear
import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner

/-! # Intrinsic Local Residual Action -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.IntrinsicShear

/-! The actual local residual coordinate equivalence is a symmetric
quadratic shear, hence has the explicit real Schwartz oscillator lift. -/

open OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction
open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionFixedShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphProjector.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)

theorem local_residual_phase_pairing (x y : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    IntrinsicGraphProjector.Intrinsic.phasePairing (IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z x)
      (IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z y) = IntrinsicGraphProjector.Intrinsic.phasePairing x y := by
  rw [IntrinsicPlaceCotangent.Intrinsic.phase_pairing_standard,IntrinsicPlaceCotangent.Intrinsic.phase_pairing_standard]
  exact IntrinsicLocalResidualEquiv.Intrinsic.local_residual_pairing B hC hG hO v z x y

theorem local_residual_positions (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) (i : Fin 6) :
    IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z x (.inl i) = x (.inl i) := by
  have he := congrFun (congrFun (IntrinsicResidualPhase.Intrinsic.residual_phase_positions B hC (Pi.single v x)) v) i
  simp only [Pi.single_eq_same] at he
  exact he

def localResidualSymmetricMatrix : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℝ 6 :=
  ⟨IntrinsicPositionFixedShear.Intrinsic.shearMatrix (IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z).toLinearMap,
    IntrinsicPositionFixedShear.Intrinsic.shear_matrix_symmetric _ (local_residual_phase_pairing B hC hG hO v z)
      (local_residual_positions B hC hG hO v z)⟩

theorem local_residual_symplectic_action (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.quadraticSymplectic (localResidualSymmetricMatrix B hC hG hO v z)) x =
      IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z x := by
  have he := IntrinsicPositionFixedShear.Intrinsic.position_fixed_formula (IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z).toLinearMap
    (local_residual_phase_pairing B hC hG hO v z) (local_residual_positions B hC hG hO v z) x
  change (Matrix.fromBlocks (1 : Matrix (Fin 6) (Fin 6) ℝ) 0
    (localResidualSymmetricMatrix B hC hG hO v z).val 1).mulVec x = _
  rw [Matrix.fromBlocks_mulVec,Matrix.one_mulVec,Matrix.zero_mulVec,Matrix.one_mulVec,add_zero]
  exact (congrArg (Sum.elim (fun i => x (.inl i))) (add_comm _ _)).trans he.symm

def localResidualRealOscillator : Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ 6 (Weil.Local.Gaussian.Construction.realCharacter 1) :=
  Weil.Local.QuadraticIntertwiner.Construction.realQuadraticOscillator 1 (localResidualSymmetricMatrix B hC hG hO v z)

theorem local_residual_real_operator_value (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ 6) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ 6) :
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ 6 (Weil.Local.Gaussian.Construction.realCharacter 1) (localResidualRealOscillator B hC hG hO v z) φ).val x =
      Weil.Local.Gaussian.Construction.realCharacter 1 (Weil.Local.FunctionsMetaplectic.Construction.quadratic (localResidualSymmetricMatrix B hC hG hO v z).val x) * φ.val x := rfl

end RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.IntrinsicShear

namespace RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.Intrinsic

/-! The actual local residual quadratic shear centralizes the actual
local SU symplectic action, as recovered from the full native Gaussian
identity. -/

open OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction
open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.IntrinsicShear

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}

def localNativeRealAction (g : Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places) : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ 6 :=
  Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) 6 (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 2 H K P (.inl (A.enumerate v))
    (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))

theorem native_phase_action_local (g : Adelic.RationalSU.ArchimedeanSU F H) (v : Fin A.places)
    (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    IntrinsicCotangentAction.Intrinsic.nativePhaseAction (A := A) (P := P) g u v =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (localNativeRealAction (A := A) (P := P) g v) (u v) := by
  have he := Weil.Local.FieldFourier.Construction.fieldSymplecticMap_action (A.real v)
    (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 2 H K P (.inl (A.enumerate v))
      (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))
    (fun i => (A.real v).symm (u v i))
  simp only [RingEquiv.apply_symm_apply] at he
  exact he.symm

variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
variable (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ) (v : Fin A.places) (z : Adelic.BallNatural.Ball)

include hψ

theorem local_residual_commutes_action (g : Adelic.RationalSU.ArchimedeanSU F H) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z
      (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (localNativeRealAction (A := A) (P := P) g v) x) =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (localNativeRealAction (A := A) (P := P) g v)
        (IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v z x) := by
  let u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 := Pi.single v x
  have he := congrFun (IntrinsicResidualPhase.Intrinsic.residual_phase_commutes B hC hO hG hψ g z u) v
  change IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B (IntrinsicCotangentAction.Intrinsic.nativePhaseAction (A := A) (P := P) g u) v =
    IntrinsicCotangentAction.Intrinsic.nativePhaseAction (A := A) (P := P) g (IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B u) v at he
  rw [← IntrinsicLocalResidualEquiv.Intrinsic.local_residual_apply B hC hG hO v z,native_phase_action_local,native_phase_action_local,
    ← IntrinsicLocalResidualEquiv.Intrinsic.local_residual_apply B hC hG hO v z] at he
  simpa only [u,Pi.single_eq_same] using he

theorem local_residual_symplectic_commutes (g : Adelic.RationalSU.ArchimedeanSU F H) :
    Commute (Weil.Local.Generators.Construction.quadraticSymplectic (IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z))
      (localNativeRealAction (A := A) (P := P) g v) := by
  change _ * _ = _ * _
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change ((Weil.Local.Generators.Construction.quadraticSymplectic (IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z)).val *
    (localNativeRealAction (A := A) (P := P) g v).val).mulVec x =
      ((localNativeRealAction (A := A) (P := P) g v).val *
        (Weil.Local.Generators.Construction.quadraticSymplectic (IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z)).val).mulVec x
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  change Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.quadraticSymplectic (IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z))
    (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (localNativeRealAction (A := A) (P := P) g v) x) =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (localNativeRealAction (A := A) (P := P) g v)
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.quadraticSymplectic (IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z)) x)
  rw [IntrinsicShear.local_residual_symplectic_action,IntrinsicShear.local_residual_symplectic_action]
  exact local_residual_commutes_action B hC hG hO hψ v z g x

end RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.Intrinsic

end

end OAI
