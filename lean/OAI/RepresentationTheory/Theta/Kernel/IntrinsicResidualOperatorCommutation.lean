import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualField
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanCentralizer

/-! # Intrinsic Residual Operator Commutation -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualOperatorCommutation.Intrinsic

noncomputable section

/-! The explicitly constructed native residual Schwartz multiplier
commutes with the actual local SU oscillator lift. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualField.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.IntrinsicShear
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanCentralizer.Intrinsic

theorem field_symplectic_map_injective {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) (n : ℕ) : Function.Injective (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e n) := by
  intro a b h
  apply Subtype.ext
  ext i j
  apply e.injective
  exact congrArg (fun g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic l n => g.val i j) h

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
variable (v : Fin A.places) (z : Adelic.BallNatural.Ball)

include hψ

local instance (w : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := borel _
local instance (w : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := ⟨rfl⟩

theorem local_residual_field_centralizes
    (g : Adelic.SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))) :
    Commute (Weil.AdelicSplitting.Vacuum.Construction.projectionAt F 6 C.ψ (.inl (A.enumerate v)) (IntrinsicLocalResidualField.Intrinsic.localResidualFieldOscillator B hC hG hO v z))
      (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 2 H K P (.inl (A.enumerate v)) (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) g)) := by
  let gA : Adelic.RationalSU.ArchimedeanSU F H := Function.update 1 (A.enumerate v) g
  have hvalue : gA (A.enumerate v) = g := Function.update_self _ _ _
  have he := IntrinsicLocalResidualAction.Intrinsic.local_residual_symplectic_commutes B hC hG hO hψ v z gA
  unfold IntrinsicLocalResidualAction.Intrinsic.localNativeRealAction at he
  rw [hvalue] at he
  have hp := IntrinsicLocalResidualField.Intrinsic.local_residual_field_projection B hC hG hO v z
  have hm : Commute
      (Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) 6
        (Weil.AdelicSplitting.Vacuum.Construction.projectionAt F 6 C.ψ (.inl (A.enumerate v)) (IntrinsicLocalResidualField.Intrinsic.localResidualFieldOscillator B hC hG hO v z)))
      (Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) 6
        (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 2 H K P (.inl (A.enumerate v))
          (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) g))) := hp.symm ▸ he
  exact (commute_map_iff (field_symplectic_map_injective (A.real v) 6)).mp hm

theorem local_residual_field_commutes (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (g : Adelic.SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))) :
    Commute (IntrinsicLocalResidualField.Intrinsic.localResidualFieldOscillator B hC hG hO v z)
      (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl (A.enumerate v)) g) :=
  IntrinsicArchimedeanCentralizer.Intrinsic.native_lift_centralizer A D hu v (IntrinsicLocalResidualField.Intrinsic.localResidualFieldOscillator B hC hG hO v z)
    (local_residual_field_centralizes B hC hG hO hψ v z) g

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualOperatorCommutation.Intrinsic
