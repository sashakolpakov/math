import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.Padic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPELLevel

/-! # Away Padic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPadic.Approximation

noncomputable section

/-! Every specified Q_q embedding evaluates the filled PEL away element
at the corresponding actual local unitary matrix. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem cmOriginalPELHomeomorph_padic (g : FiniteAway.Approximation.CMFiniteSU E P hP) (i j : Fin 3) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ ((AwayPELLevel.Approximation.cmOriginalPELHomeomorph E P hP g).val (Pi.single j 1) i) =
      (ActiveProjection.Approximation.cmActiveSL E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
        (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (g (ActivePlace.Approximation.cmActivePlace E σ))).val i j := by
  have he := UnitaryLinear.Approximation.matrixPELUnitary_entry E P
    (FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
      (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1 g) i j
  exact (congrArg (Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ) he).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) (Padic q) => M i j)
      (CM.Padic.Approximation.cmFiniteTensorUnitary_padic E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
        (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1 g))

variable (w : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield E))

theorem cmAwayToPEL_padic (g : FiniteAway.Approximation.CMFiniteAway E P hP w) (i j : Fin 3) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ ((AwayPELLevel.Approximation.cmAwayToPEL E P hP w g).val (Pi.single j 1) i) =
      (ActiveProjection.Approximation.cmActiveSL E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
        (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (RestrictedInsert.Approximation.restrictedInsertPlace _ w g (ActivePlace.Approximation.cmActivePlace E σ))).val i j :=
  cmOriginalPELHomeomorph_padic E σ P hP (RestrictedInsert.Approximation.restrictedInsertPlace _ w g) i j

theorem cmAwayToPEL_padic_same (h : ActivePlace.Approximation.cmActivePlace E σ = w)
    (g : FiniteAway.Approximation.CMFiniteAway E P hP w) (i j : Fin 3) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ ((AwayPELLevel.Approximation.cmAwayToPEL E P hP w g).val (Pi.single j 1) i) =
      (1 : Matrix (Fin 3) (Fin 3) (Padic q)) i j := by
  have hv : RestrictedInsert.Approximation.restrictedInsertPlace _ w g (ActivePlace.Approximation.cmActivePlace E σ) = 1 := by
    subst w
    exact RestrictedInsert.Approximation.restrictedInsertPlace_same _ _ g
  have hm := congrArg (ActiveProjection.Approximation.cmActiveSL E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)) hv
  have hm' := hm.trans (map_one (ActiveProjection.Approximation.cmActiveSL E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)))
  exact (cmAwayToPEL_padic E σ P hP w g i j).trans
    (congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (Padic q) => A.val i j) hm')

theorem cmAwayToPEL_padic_rational_other (h : ActivePlace.Approximation.cmActivePlace E σ ≠ w)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (i j : Fin 3) :
    Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E σ
      ((AwayPELLevel.Approximation.cmAwayToPEL E P hP w (FiniteAway.Approximation.cmRationalFiniteAway E P hP w γ)).val (Pi.single j 1) i) =
      σ (γ.val.val i j) := by
  have hv := RestrictedInsert.Approximation.restrictedInsertPlace_other _ w (FiniteAway.Approximation.cmRationalFiniteAway E P hP w γ)
    (ActivePlace.Approximation.cmActivePlace E σ) h
  have hm := congrArg (ActiveProjection.Approximation.cmActiveSL E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)) hv
  have hr := ActiveProjection.Approximation.cmActiveSL_original E σ P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1 γ
  have ha := hm.trans hr
  exact (cmAwayToPEL_padic E σ P hP w (FiniteAway.Approximation.cmRationalFiniteAway E P hP w γ) i j).trans
    (congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (Padic q) => A.val i j) ha)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.AwayPadic.Approximation
