import OAI.Geometry.ComplexBall.ArithmeticQuotientConditional
import OAI.Geometry.ComplexBall.ArithmeticQuotientFree

/-! # Arithmetic Quotient Of -/

namespace OAI.Geometry.ComplexBall.ArithmeticQuotientOf

noncomputable section

open scoped Classical _root_.Manifold
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.NumberField

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

theorem existence_of_compact_ball_quotients
    [IsGalois ℚ E]
    (μ : E →+* ℂ)
    -- There is a real place other than the one underlying μ.
    (h_other_place :
      ∃ ν : E →+* ℂ,
        ν ≠ μ ∧ ν ≠ (starRingEnd ℂ).comp μ) :
    ∃ b : E,
      NumberField.IsCMField.complexConj E b = b ∧
      b ≠ 0 ∧
      -- Signature (2,1) at μ and (3,0) at every other real place.
      (μ b).re < 0 ∧
      (∀ ν : E →+* ℂ,
        ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ →
          0 < (ν b).re) ∧
      -- Nondegeneracy and Hermitian anisotropy over E.
      (∀ x : ArithmeticQuotientEquationsData.Vec E,
        (∀ y : ArithmeticQuotientEquationsData.Vec E, ArithmeticQuotientEquationsData.hermitian b x y = 0) → x = 0) ∧
      (∀ x : ArithmeticQuotientEquationsData.Vec E, ArithmeticQuotientEquationsData.hermitian b x x = 0 → x = 0) ∧
      -- Every initial integer principal level has a suitable refinement.
      (∀ N₀ : ℕ, 0 < N₀ →
        ∃ N : ℕ, 0 < N ∧ N₀ ∣ N ∧
          (∀ g : ArithmeticQuotientEquationsData.Mat E, ArithmeticQuotientEquationsData.principalLevel b N g →
            ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
          ∃ R : Setoid (ArithmeticQuotientEquationsData.NegativeVectors b μ),
            (∀ z w, R.r z w ↔ ArithmeticQuotientEquationsData.orbitRelation b μ N z w) ∧
            CompactSpace (Quotient R) ∧
            T2Space (Quotient R) ∧
            SecondCountableTopology (Quotient R) ∧
            ConnectedSpace (Quotient R) ∧
            ∃ atlas : ChartedSpace (Fin 2 → ℂ) (Quotient R),
              letI := atlas
              IsManifold 𝓘(ℂ, Fin 2 → ℂ) 1 (Quotient R) ∧
              -- The natural projection is a holomorphic submersion.
              ∀ z : ArithmeticQuotientEquationsData.NegativeVectors b μ,
                MDifferentiableAt
                  𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, Fin 2 → ℂ)
                  (ArithmeticQuotientEquationsData.projection b μ R z) z.val ∧
                Function.Surjective
                  (mfderiv
                    𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, Fin 2 → ℂ)
                    (ArithmeticQuotientEquationsData.projection b μ R z) z.val)) := by
  exact ArithmeticQuotientConditional.existence_of_compact_ball_quotients_conditional
    (ArithmeticQuotientFree.weakApproximationInput_proved E) ArithmeticQuotientFree.arithmeticLatticeInput_proved
    (ArithmeticQuotientFree.torsionFreeLevelsInput_proved E) μ h_other_place

end

end OAI.Geometry.ComplexBall.ArithmeticQuotientOf
