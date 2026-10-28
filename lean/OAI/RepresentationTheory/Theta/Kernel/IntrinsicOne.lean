import OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf

/-! # Intrinsic One -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicOne.Intrinsic

noncomputable section

/-! The complete native ThetaOneForms prerequisite, retaining the full AdelicTheta
statement and every comparison, oscillator, theta, descent, and spanning
conclusion for the same witnesses. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData

def NativeThetaOneFormsStatement : Prop :=
  ∀ (_h_C3_6 : Adelic.Data.CompleteStatement)
    (F : Type) [Field F] [NumberField F] (d : F) (hq : d ≠ 0 ∧ ¬ IsSquare d)
    (H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (_hH : H.val.conjTranspose = H.val) (_hK : K.val.conjTranspose = -K.val)
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (_hc : Continuous ψ) (_hu : ∀ x, ‖ψ x‖ = 1)
    (_hn : ∃ x, ψ x ≠ 1) (_hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K) (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K)
    (_hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ),
    ∃ C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1, C.ψ = ψ ∧ Adelic.Data.CharacterConclusion F d 3 1 C ∧
      ∃ D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hq.1 C P,
        Adelic.Data.AdelicConclusion F d 3 1 H K hq.1 C P D ∧ Adelic.Data.FiniteConclusion F d 3 1 H K hq.1 C P D ∧
        ∃ B : Adelic.DataTheta.ComparisonData F H K A,
          Adelic.DataTheta.CoordinateIdentification B P ∧ Adelic.DataTheta.GeometryIdentification B ∧
          Adelic.DataTheta.OscillatorIdentification B P hq.1 C D ∧ Adelic.SiegelBranchData.SiegelBranchExtension B P hq.1 C D ∧
          Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hq.1 C D ∧ Adelic.DataTheta.Descent.ThetaConstruction B ∧
          Adelic.DataTheta.Descent.RationalHeckeCovariance B P hq.1 C D ∧ Adelic.DataTheta.Descent.CongruenceDescent B P hq.1 C D ∧
          OneFormsIntrinsicOf.Intrinsic.NativeConclusion B P hq.1 C D

theorem full_native_ThetaOneForms : NativeThetaOneFormsStatement :=
  OneFormsIntrinsicOf.Intrinsic.theta_one_forms_of_complete_AdelicTheta

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicOne.Intrinsic
