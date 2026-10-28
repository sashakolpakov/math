import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveInverse
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayLevelTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert

/-! # Source Active Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.SourceActiveLevel.Approximation

noncomputable section

/-! An auxiliary open active subgroup puts the same rational element in
the prescribed source level whenever its filled away factor lies there. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]

theorem cmHermitian_local_hermitian
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
    (w : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (maximalRealSubfield E)) :
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
      (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) w).val.conjTranspose =
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
      (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) w).val := by
  change (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit _ _ (ThetaCycle.DiagonalFrame.CM.diagonalHermitianUnit _ _ _) _).val.conjTranspose =
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit _ _ (ThetaCycle.DiagonalFrame.CM.diagonalHermitianUnit _ _ _) _).val
  rw [ThetaCycle.GlobalFrames.CM.localized_diagonal_hermitian]
  exact ThetaCycle.DiagonalFrame.CM.diagonal_hermitian_conjugateTranspose _ _

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)

def cmOriginalActiveInverse : Matrix.SpecialLinearGroup (Fin 3) (Padic q) →ₜ*
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP).val
      (.inr (ActivePlace.Approximation.cmActivePlace E σ))) :=
  ActiveInverse.Approximation.cmActiveSLInverse E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (cmHermitian_local_hermitian E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
      P.b hP.2.1 hP.2.2.1 (.inr (ActivePlace.Approximation.cmActivePlace E σ)))

theorem cmOriginalActiveInverse_rational (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    cmOriginalActiveInverse E P hP σ (Matrix.SpecialLinearGroup.map σ γ.val) =
      FiniteAway.Approximation.cmRationalFiniteSU E P hP γ (ActivePlace.Approximation.cmActivePlace E σ) := by
  have h := ActiveInverse.Approximation.cmActiveSLInverse_left E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (cmHermitian_local_hermitian E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
      P.b hP.2.1 hP.2.2.1 (.inr (ActivePlace.Approximation.cmActivePlace E σ)))
    (FiniteAway.Approximation.cmRationalFiniteSU E P hP γ (ActivePlace.Approximation.cmActivePlace E σ))
  have hg := ActiveProjection.Approximation.cmActiveSL_original E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1 γ
  exact (congrArg (cmOriginalActiveInverse E P hP σ) hg.symm).trans h

def cmActiveSourceInclusion : Matrix.SpecialLinearGroup (Fin 3) (Padic q) →ₜ*
    FiniteAway.Approximation.CMFiniteSU E P hP :=
  (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlaceContinuous _ (ActivePlace.Approximation.cmActivePlace E σ)).comp (cmOriginalActiveInverse E P hP σ)

variable (K : OpenSubgroup (FiniteAway.Approximation.CMFiniteSU E P hP))
  (J : OpenSubgroup (Matrix.SpecialLinearGroup (Fin 3) (Padic q)))

def cmSourceActiveLevel : OpenSubgroup (Matrix.SpecialLinearGroup (Fin 3) (Padic q)) :=
  RestrictedInsert.Approximation.restrictedActiveLevel _ (ActivePlace.Approximation.cmActivePlace E σ) K J (cmOriginalActiveInverse E P hP σ)

theorem cmSourceActiveLevel_rational_mem (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (hactive : Matrix.SpecialLinearGroup.map σ γ.val ∈ cmSourceActiveLevel E P hP σ K J)
    (haway : RestrictedInsert.Approximation.restrictedInsertPlace _ (ActivePlace.Approximation.cmActivePlace E σ)
      (FiniteAway.Approximation.cmRationalFiniteAway E P hP (ActivePlace.Approximation.cmActivePlace E σ) γ) ∈ K) :
    FiniteAway.Approximation.cmRationalFiniteSU E P hP γ ∈ K :=
  RestrictedInsert.Approximation.restrictedActiveLevel_mem _ (ActivePlace.Approximation.cmActivePlace E σ) K J (cmOriginalActiveInverse E P hP σ)
    (FiniteAway.Approximation.cmRationalFiniteSU E P hP γ) (Matrix.SpecialLinearGroup.map σ γ.val)
    (cmOriginalActiveInverse_rational E P hP σ γ) hactive haway

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.SourceActiveLevel.Approximation
