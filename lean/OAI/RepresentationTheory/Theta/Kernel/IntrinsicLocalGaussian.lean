import OAI.RepresentationTheory.Theta.Kernel.IntrinsicOscillatorGaussian
import OAI.RepresentationTheory.Weil.Local.FieldOscillator
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Intrinsic Local Gaussian -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussian.Intrinsic

noncomputable section

/-! Gaussian-line transport in actual real completion presentations,
using the native standard additive-character normalization. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Weil.Local.FieldOscillator.Construction
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicOscillatorGaussian.Intrinsic

theorem real_character_gaussian_test {n : ℕ} (η : AddChar ℝ ℂ)
    (hη : η = Weil.Local.Gaussian.Construction.realCharacter 1) (a : Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ n η) (P : Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (hφ : φ.val = Weil.Local.SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix) :
    ∃ c : ℂ, c ≠ 0 ∧ (a.val.2 φ).val =
      c • Weil.Local.SiegelGaussian.Construction.siegelGaussian (P.act (Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ n η a)).quadraticMatrix := by
  subst η
  exact IntrinsicOscillatorGaussian.Intrinsic.oscillator_gaussian_test a P φ hφ

theorem field_oscillator_gaussian_test
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (e : k ≃+* ℝ) (he : Continuous e) (hi : Continuous e.symm)
    (ψ : AddChar k ℂ) (hψ : Weil.Local.FieldFourier.Construction.fieldCharacter e ψ = Weil.Local.Gaussian.Construction.realCharacter 1)
    (a : Weil.Local.FunctionsMetaplectic.Construction.Oscillator k n ψ) (P : Weil.Local.SiegelGaussian.Construction.PositiveLagrangianFrame n) (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hφ : (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n => φ.val (fun i => e.symm (x i))) = Weil.Local.SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix) :
    ∃ c : ℂ, c ≠ 0 ∧
      (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n => (a.val.2 φ).val (fun i => e.symm (x i))) =
        c • Weil.Local.SiegelGaussian.Construction.siegelGaussian (P.act (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e n (Weil.Local.OscillatorProjection.Construction.oscillatorProjection k n ψ a))).quadraticMatrix := by
  let T := Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi n)
  have hT : (T φ).val = Weil.Local.SiegelGaussian.Construction.siegelGaussian P.quadraticMatrix := hφ
  obtain ⟨c,hc,h⟩ := real_character_gaussian_test (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) hψ
    (Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport e he hi n ψ a) P (T φ) hT
  rw [Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport_projection,Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport_apply] at h
  exact ⟨c,hc,h⟩

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d m H K)

theorem standard_arch_field_character (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ) (v : Fin A.places) :
    Weil.Local.FieldFourier.Construction.fieldCharacter (A.real v) (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl (A.enumerate v))) = Weil.Local.Gaussian.Construction.realCharacter 1 := by
  ext t
  change Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl (A.enumerate v)) ((A.real v).symm t) = Weil.Local.Gaussian.Construction.realCharacter 1 t
  rw [hψ v t,Weil.Local.Gaussian.Construction.realCharacter_apply]
  congr 1
  push_cast
  ring

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussian.Intrinsic
