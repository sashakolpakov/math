import OAI.RepresentationTheory.Theta.Adelic.Prerequisites
import OAI.RepresentationTheory.Theta.Adelic.Data

/-! # Theta Ball -/

namespace OAI

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaBall.CM
section

/-! The complete named AdelicTheta theorem type, including its full prerequisite
record and all general, split, and geometric theta conclusions. -/

def AdelicThetaInput : Prop :=
  RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0} →
    RepresentationTheory.Theta.Adelic.Data.CompleteStatement

end

noncomputable section

/-! Retain every conclusion of the full AdelicTheta ball specialization. -/

open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData

variable (F : Type) [Field F] [NumberField F] (a : F) (m : ℕ)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (ha : a ≠ 0) (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F a 3 m H K)
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F a m H K)

def Output : Prop :=
  ∃ C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F a 3 m, C.ψ = ψ ∧ RepresentationTheory.Theta.Adelic.Data.CharacterConclusion F a 3 m C ∧
    ∃ D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F a 3 m H K ha C P,
      RepresentationTheory.Theta.Adelic.Data.AdelicConclusion F a 3 m H K ha C P D ∧ RepresentationTheory.Theta.Adelic.Data.FiniteConclusion F a 3 m H K ha C P D ∧
      ∃ T : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A,
        RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T P ∧ RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T ∧ RepresentationTheory.Theta.Adelic.DataTheta.OscillatorIdentification T P ha C D ∧
        RepresentationTheory.Theta.Adelic.SiegelBranchData.SiegelBranchExtension T P ha C D ∧ RepresentationTheory.Theta.Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P ha C D ∧
        RepresentationTheory.Theta.Adelic.DataTheta.Descent.ThetaConstruction T ∧ RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance T P ha C D ∧ RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent T P ha C D

theorem of_full (hAdelicTheta : AdelicThetaInput) (inputs : RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0})
    (hnot : ¬ IsSquare a) (hm : m = 1 ∨ m = 2)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) (hn : ∃ x, ψ x ≠ 1)
    (hp : ∀ x : F, ψ (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (hS : RepresentationTheory.Theta.Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ) : Output F a m H K ha ψ P A :=
  (hAdelicTheta inputs).2.2 F a ⟨ha, hnot⟩ m hm H K hH hK ψ hc hu hn hp P A hS

end
end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaBall.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaBall.CM.Elimination

noncomputable section

/-! Eliminate the complete AdelicTheta ball output when constructing a finite
representation. The full output remains the premise. -/

open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent

variable (F : Type) [Field F] [NumberField F] (a : F) (m : ℕ)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (ha : a ≠ 0) (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F a 3 m H K)
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F a m H K)

theorem finite_representation {p : Prop} (h : Output F a m H K ha ψ P A)
    (k : ∀ (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F a 3 m) (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F a 3 m H K ha C P),
      RepresentationTheory.Theta.Adelic.Data.FiniteConclusion F a 3 m H K ha C P D → ∀ T : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A,
        RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T P → RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T → RepresentationTheory.Theta.Adelic.DataTheta.OscillatorIdentification T P ha C D →
          RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance T P ha C D → p) : p := by
  obtain ⟨C, _, _, D, _, hD, T, hT, hG, hO, _, _, _, hCov, _⟩ := h
  exact k C D hD T hT hG hO hCov

end

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaBall.CM.Elimination

end OAI
