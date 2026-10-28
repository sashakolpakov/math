import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualOperatorCommutation
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperatorRecovery
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology

/-! # Intrinsic Residual Family -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualFamily.IntrinsicFamily

noncomputable section

/-! The actual residual oscillator family and its conjugates of every
compact multiplicity choice, with covariance at the original finite level. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualField.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualOperatorCommutation.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperatorRecovery.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicConjugated OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicCommutingArch
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

theorem conjugate_pair_one {G J E : Type*} [Group G] [Group J] [Group E]
    (s : G × J →* E) (b : E) (w : J) (hw : w = 1) : b⁻¹ * s (1,w) * b = 1 := by
  subst w
  change b⁻¹ * s 1 * b = 1
  rw [map_one,mul_one,inv_mul_cancel]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)

local instance (w : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := borel _
local instance (w : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := ⟨rfl⟩

def residualOscillatorFamily : ∀ w : NumberField.InfinitePlace F, Weil.AdelicSplitting.Vacuum.Construction.CoverAt F 6 C.ψ (.inl w) :=
  Equiv.piCongrLeft (fun w => Weil.AdelicSplitting.Vacuum.Construction.CoverAt F 6 C.ψ (.inl w)) A.enumerate
    (fun v => IntrinsicLocalResidualField.Intrinsic.localResidualFieldOscillator B hC hG hO v IntrinsicBallTopology.Intrinsic.origin)

theorem residual_family_at (v : Fin A.places) :
    residualOscillatorFamily B hC hG hO (A.enumerate v) =
      IntrinsicLocalResidualField.Intrinsic.localResidualFieldOscillator B hC hG hO v IntrinsicBallTopology.Intrinsic.origin :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem residual_family_commutes (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D) (w : NumberField.InfinitePlace F)
    (g : Adelic.SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl w))) :
    Commute (residualOscillatorFamily B hC hG hO w)
      (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl w) g) := by
  obtain ⟨v,rfl⟩ := A.enumerate.surjective w
  rw [residual_family_at]
  exact IntrinsicResidualOperatorCommutation.Intrinsic.local_residual_field_commutes B hC hG hO hψ v IntrinsicBallTopology.Intrinsic.origin hu g

def compactResidualFamily (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (w : NumberField.InfinitePlace F) : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F 6 C.ψ (.inl w) :=
  IntrinsicMultiplicityOperator.IntrinsicConjugated.conjugatedMultiplicityFamily F H K hd P C D (residualOscillatorFamily B hC hG hO)
    (IntrinsicCompactOperatorRecovery.Intrinsic.operatorsOfChoice A p).val w

theorem compact_residual_distinguished (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) :
    compactResidualFamily B hC hG hO p (A.enumerate A.distinguished) = 1 := by
  exact conjugate_pair_one (D.atPlace (.inl (A.enumerate A.distinguished))).toMonoidHom
    (residualOscillatorFamily B hC hG hO (A.enumerate A.distinguished))
    ((IntrinsicCompactOperatorRecovery.Intrinsic.operatorsOfChoice A p).val (A.enumerate A.distinguished)) (IntrinsicCompactOperatorRecovery.Intrinsic.operatorsOfChoice A p).property

theorem compact_residual_commutes (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (w : NumberField.InfinitePlace F) (g : Adelic.SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl w))) :
    Commute (compactResidualFamily B hC hG hO p w)
      (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl w) g) :=
  IntrinsicMultiplicityOperator.IntrinsicConjugated.conjugated_multiplicity_commutes F H K hd P C D _
    (residual_family_commutes B hC hG hO hψ hu) (IntrinsicCompactOperatorRecovery.Intrinsic.operatorsOfChoice A p).val w g

theorem compact_residual_theta_fixed_level (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (g : Adelic.SpecialUnitary.SU H.val) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hf : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) :
    Adelic.ThetaEvaluation.theta F 6
      (IntrinsicMultiplicityOperator.IntrinsicCommutingArch.archOperator F C (compactResidualFamily B hC hG hO p)
        (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D (Adelic.RationalSU.rationalArchimedeanSU F H g) φ)) f =
      Adelic.ThetaEvaluation.theta F 6 (IntrinsicMultiplicityOperator.IntrinsicCommutingArch.archOperator F C (compactResidualFamily B hC hG hO p) φ) f :=
  IntrinsicMultiplicityOperator.IntrinsicCommutingArch.arch_operator_theta_fixed_level F H K hd P C D hns hH hK _
    (compact_residual_commutes B hC hG hO hψ hu p) g φ f hf

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualFamily.IntrinsicFamily
