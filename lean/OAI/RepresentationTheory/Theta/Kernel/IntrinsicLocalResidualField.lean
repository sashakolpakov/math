import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussian
import OAI.RepresentationTheory.Weil.Local.FieldGeneratorMatrices
import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators

/-! # Intrinsic Local Residual Field -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualField.Intrinsic

noncomputable section

/-! The actual residual quadratic Schwartz operator in the native
completion field, with exact projection and real-coordinate values. -/

open OAI.RepresentationTheory.Weil.Local.FieldGeneratorMatrices.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators.Construction
open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.IntrinsicShear OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussian.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)

local instance (w : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := borel _
local instance (w : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := ⟨rfl⟩

def localResidualFieldMatrix : Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) 6 :=
  Weil.Local.FieldGeneratorMatrices.Construction.fieldSymmetricMatrix (A.real v).symm (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z)

def localResidualFieldOscillator : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F 6 C.ψ (.inl (A.enumerate v)) :=
  Weil.AdelicSplitting.QuadraticGenerators.Construction.quadraticAtPlace F 6 C.ψ C.ψ_unitary C.ψ_continuous (.inl (A.enumerate v))
    (localResidualFieldMatrix B hC hG hO v z)

theorem local_residual_field_projection :
    Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) 6
      (Weil.AdelicSplitting.Vacuum.Construction.projectionAt F 6 C.ψ (.inl (A.enumerate v)) (localResidualFieldOscillator B hC hG hO v z)) =
      Weil.Local.Generators.Construction.quadraticSymplectic (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z) := by
  rw [show Weil.AdelicSplitting.Vacuum.Construction.projectionAt F 6 C.ψ (.inl (A.enumerate v)) (localResidualFieldOscillator B hC hG hO v z) =
    Weil.Local.Generators.Construction.quadraticSymplectic (localResidualFieldMatrix B hC hG hO v z) from rfl,Weil.Local.FieldGeneratorMatrices.Construction.fieldSymplecticMap_quadratic]
  congr 1
  apply Subtype.ext
  ext i j
  exact (A.real v).apply_symm_apply _

theorem local_residual_field_operator_value (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) 6) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ 6) :
    (Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (localResidualFieldOscillator B hC hG hO v z) φ).val
      (fun i => (A.real v).symm (x i)) =
        Weil.Local.Gaussian.Construction.realCharacter 1 (Weil.Local.FunctionsMetaplectic.Construction.quadratic (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z).val x) *
          φ.val (fun i => (A.real v).symm (x i)) := by
  change Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inl (A.enumerate v))
    (Weil.Local.FunctionsMetaplectic.Construction.quadratic ((IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z).val.map (A.real v).symm)
      (fun i => (A.real v).symm (x i))) * φ.val (fun i => (A.real v).symm (x i)) = _
  have hq := Weil.AdelicSplitting.FieldTransport.LocalAnalysis.quadratic_field_map (A.real v).symm.toRingHom
    (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z).val x
  change Weil.Local.FunctionsMetaplectic.Construction.quadratic ((IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z).val.map (A.real v).symm)
      (fun i => (A.real v).symm (x i)) =
    (A.real v).symm (Weil.Local.FunctionsMetaplectic.Construction.quadratic (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z).val x) at hq
  rw [hq]
  have he := congrArg (fun ψ : AddChar ℝ ℂ =>
    ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v z).val x))
    (IntrinsicLocalGaussian.Intrinsic.standard_arch_field_character A C.ψ hψ v)
  exact congrArg (fun a : ℂ => a * φ.val (fun i => (A.real v).symm (x i))) he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualField.Intrinsic
