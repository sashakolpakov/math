import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HilbertConstructionInterface
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral
import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

/-! # Prerequisite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Prerequisite

noncomputable section

/-! Explicit prerequisite types for conditional ReferenceFamily. Each retains the
whole committed statement, including its original universal scope. These
definitions do not assert or prove the prerequisites. The HilbertConstruction interface
and its bundled pure-input equivalence are in StatementInterface.
Original-context type comparisons remain part of final validation.
-/

open scoped BigOperators

universe u v

/-- CongruenceLevel uses the literal Hermitian form imported by its committed statement. -/
theorem referenceHermitian_eq_committed
    {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
    (b : E) (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y = Geometry.ComplexBall.ArithmeticQuotientEquationsData.hermitian b x y := rfl

/-- The reference-fiber projectivity interface is the same closed
holomorphic-embedding condition used in the ThetaConstruction analytic torus model. -/
theorem referenceProjectivity_iff_native
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] (Λ : AddSubgroup V) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus V Λ ↔
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.IsProjectiveComplexTorus V Λ := Iff.rfl

/-- Both full committed TorsionFreeLevel conclusions, with arbitrary lattices, levels,
subgroups, action spaces, and finite point stabilizers. -/
def TorsionFreeLevelFullStatement : Prop :=
  (∀ (E : Type u) [Field E] [NumberField E] [Algebra ℚ E]
      [NumberField.IsCMField E]
      (b : E) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)), NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ →
      ∀ (N₀ : ℕ), 0 < N₀ →
        ∃ N : ℕ, 3 ≤ N ∧ N₀ ∣ N ∧
          ∀ M : ℕ, 0 < M → N ∣ M →
            ∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ M g →
              ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
  (∀ (E : Type u) [Field E] [NumberField E] [Algebra ℚ E]
      [NumberField.IsCMField E]
      (b : E) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)), NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ →
      ∀ (N : ℕ), 3 ≤ N →
        ∀ (Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (X : Type v) [MulAction Γ X],
          (∀ x : X, (MulAction.stabilizer Γ x : Set Γ).Finite) →
          ∀ (g : Γ) (x : X), NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ N (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) →
            g • x = x → g = 1)

/-- The full committed NormOneUnits assertion for all norm-one integral units. -/
def NormOneUnitsFullStatement : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E] [NumberField.IsCMField E]
    (a : (NumberField.RingOfIntegers E)ˣ),
    ((a : NumberField.RingOfIntegers E) : E) *
      NumberField.IsCMField.complexConj E ((a : NumberField.RingOfIntegers E) : E) = 1 →
    ∃ n : ℕ, 0 < n ∧ a ^ n = 1

/-- All three committed ThetaConstruction conclusions on the marked analytic torus
model, for every alternating nondegenerate integral polarization matrix.
No algebraic-family or moduli-chart comparison is included as an input. -/
def ThetaConstructionFullStatement : Prop :=
  ∀ (g : ℕ) (E : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g), E.transpose = -E → E.det ≠ 0 →
    (∀ P : Submodule ℂ (Picard.ThetaConstruction.DefinitionsIntegral.CVec g),
      Picard.ThetaConstruction.DefinitionsIntegral.CompatiblePositivePeriod E P ↔
        ∃ A : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g E, A.periodMap.ker = P) ∧
    (∀ A B : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g E,
      A.periodMap.ker = B.periodMap.ker ↔
        ∃ e : Picard.ThetaConstruction.DefinitionsIntegral.Tangent g ≃ₗ[ℂ] Picard.ThetaConstruction.DefinitionsIntegral.Tangent g,
          ∀ w, e (A.periodMap w) = B.periodMap w) ∧
    (∀ (A : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g E) (M : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g),
      Picard.ThetaConstruction.DefinitionsIntegral.InducesHolomorphicEndomorphism A M ↔
        ∀ w ∈ A.periodMap.ker, Picard.ThetaConstruction.DefinitionsIntegral.matrixAction M w ∈ A.periodMap.ker)

/-- The full committed CongruenceLevel reference-datum assertion. The chosen
reference signs, lattice, trace form, action, period family, and arbitrarily
deep torsion-free levels are retained at their original scopes. -/
def CongruenceLevelFullStatement : Prop :=
  ∀ (E : Type u) (Place : Type v)
      [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
      [Fintype Place] [IsGalois ℚ E]
      (σ : Place → E →ₐ[ℚ] ℂ),
    Function.Bijective
      (fun p : Place × Bool => if p.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1) →
    ∀ (μ : Place) (b : E),
      NumberField.IsCMField.complexConj E b = b → b ≠ 0 →
      (σ μ b).re < 0 →
      (∀ τ, τ ≠ μ → 0 < (σ τ b).re) →
    ∀ dref : Place → Bool,
    let B := Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b])
    let O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart :=
      {z | (B μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0}
    ∃ (δ : E) (m : ℕ) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
      (ℱ : Geometry.ComplexBall.PrescribedSignsB.BallChart → Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place)),
      δ ≠ 0 ∧ NumberField.IsCMField.complexConj E δ = -δ ∧ 0 < m ∧
      let ψ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E → ℚ :=
        fun x y => (m : ℚ) * Algebra.trace ℚ E (δ * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, ψ x y = (n : ℚ)) ∧
      (∀ x, ψ x x = 0) ∧
      (∀ x, (∀ y, ψ x y = 0) → x = 0) ∧
      (∀ (a : E) (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
        ψ (a • x) y = ψ x (NumberField.IsCMField.complexConj E a • y)) ∧
      (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E,
        (∀ x y, ψ (g x) (g y) = ψ x y) ↔
        (∀ x y, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b (g x) (g y) = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)) ∧
      Geometry.ComplexBall.PrescribedSignsB.HolomorphicFamily O (3 * Fintype.card Place) ℱ ∧
      (∀ z ∈ O,
        (∀ w, w ∈ ℱ z ↔ Geometry.ComplexBall.PrescribedSignsB.Prescribed B μ dref z w) ∧
        NumberTheory.ArithmeticGroups.Data.CongruenceLevel.AnalyticPolarizedFiber σ Λ ψ (ℱ z)) ∧
      (∀ N₀ : ℕ, 0 < N₀ →
        ∃ N : ℕ, 3 ≤ N ∧ N₀ ∣ N ∧
          ∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ N g →
            ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Prerequisite
