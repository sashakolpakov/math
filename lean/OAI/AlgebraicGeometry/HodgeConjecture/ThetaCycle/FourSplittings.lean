import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSplitting
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LinePeriods

/-! # Four Splittings -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FourSplittings.CM

noncomputable section

/-! The four given CM patterns determine the old and new signs. The
new lines are rational orthogonal lines in the original multiplicity
space, and the original two actual line periods use those same coefficients. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open _root_.Module

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def thetaSign (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    Gal(K/ℚ) → Bool := fun τ => v.val τ⁻¹

def initialThetaSigns
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    Fin 2 → Gal(K/ℚ) → Bool := ![thetaSign K (v 0), thetaSign K (v 1)]

def newThetaSigns
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)) :
    Fin 2 → Gal(K/ℚ) → Bool := ![thetaSign K (v 2), thetaSign K (v 3)]

omit [IsGalois ℚ K] in
theorem four_theta_sign_balance
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (hb : ∀ τ, ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
      ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)) (τ : Gal(K/ℚ)) :
    ComplexMultiplication.SignSwitch.CM.signValue (initialThetaSigns K v 0 τ) + ComplexMultiplication.SignSwitch.CM.signValue (initialThetaSigns K v 1 τ) =
      ComplexMultiplication.SignSwitch.CM.signValue (newThetaSigns K v 0 τ) + ComplexMultiplication.SignSwitch.CM.signValue (newThetaSigns K v 1 τ) := hb τ⁻¹

theorem exists_four_pattern_splittings
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (hb : ∀ τ, ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
      ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (hi : ∀ i, (v i).val 1 = true) :
    ∃ P : Lagrangians.CM.LagrangianPair K B places
        (fun i τ => initialThetaSigns K v i (places.representative τ)),
      ∃ L : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (initialThetaSigns K v i),
        (∀ i, (L i).coordinates.a = P.a i ∧ (L i).coordinates.delta = P.delta) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K),
            Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b 0) (b 1) = 0 ∧
            (∀ i, Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b i) (b i) ≠ 0) ∧
            (∀ y, y ∈ Submodule.span K {b 1} ↔ Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b 0) y = 0) ∧
            (∀ i τ, 0 < (ComplexMultiplication.SignSwitch.CM.signValue (newThetaSigns K v i (places.representative τ)) : ℝ) *
              (-(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).im) *
                (HeckeCycles.ReferenceDatum.CM.embeddings K places τ (Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian P.a (b i) (b i))).re) ∧
            ∀ τ, dist
              (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K places τ) b
                (fun i => newThetaSigns K v i (places.representative τ)))
              (Analysis.DifferentialForms.Coordinates.LocalApproximation.compactPeriod (HeckeCycles.ReferenceDatum.CM.embeddings K places τ)
                (Pi.basisFun K (Fin 2))
                (fun i => initialThetaSigns K v i (places.representative τ))) < ε := by
  obtain ⟨P⟩ := Lagrangians.CM.exists_lagrangian_pair K B places
    (fun i τ => initialThetaSigns K v i (places.representative τ))
  choose L hL using (fun i => LinePeriods.CM.exists_line_period K (initialThetaSigns K v) P i)
  refine ⟨P, L, hL, ?_⟩
  have hμ : ∀ i, initialThetaSigns K v i (places.representative places.distinguished) = true := by
    intro i
    fin_cases i <;> simp [initialThetaSigns, thetaSign, places.identity, hi]
  have hs := (CoefficientSigns.CM.multiplicity_sign_orientation K _ P hμ).2
  intro ε hε
  exact RationalSplitting.CM.rational_splitting_approximation
    (fun w hn hd => NumberTheory.Approximation.Weak.HodgeWeakApproximation.weak_approximation K w hn hd)
    (HeckeCycles.ReferenceDatum.CM.embeddings K places) (HeckeCycles.ReferenceDatum.CM.embeddings_complete K places) places.distinguished P.a
    (fun i => (P.a_sign i).2.1) (fun i => (P.a_sign i).1)
    (fun i τ => initialThetaSigns K v i (places.representative τ))
    (fun i τ => newThetaSigns K v i (places.representative τ))
    (fun τ => four_theta_sign_balance K v hb (places.representative τ))
    (fun τ => -(HeckeCycles.ReferenceDatum.CM.embeddings K places τ P.delta).im) hs ε hε

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FourSplittings.CM
