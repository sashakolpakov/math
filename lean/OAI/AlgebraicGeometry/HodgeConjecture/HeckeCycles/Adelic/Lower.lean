import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Quadratic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Fourier

/-! # Lower -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Lower.CM

noncomputable section

/-! Actual adelic lower lifts are exact conjugates of the upper
quadratic action by the actual adelic Fourier automorphism. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
variable (n : ℕ)

def lower (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n :=
  AdelicPairGroup.CM.assemble (Constructed.RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))
    (Real.BareGenerators.CM.lower n ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩,
      Finite.IntegralVacuum.CM.LowerBare.lowerLift (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hB.map _))

theorem lower_projection_matrix (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    (Constructed.ConstructedAdelicGroup.CM.projection n (lower n B hB)).val = Matrix.fromBlocks 1 0 B 1 := by
  change (AdelicPairGroup.CM.projection _ _ (AdelicPairGroup.CM.assemble _ _ _)).val = _
  rw [AdelicPairGroup.CM.projection_assemble]
  change SymplecticProduct.CM.pairMatrix
    (Real.SchrodingerAction.CM.projection n (Real.BareGenerators.CM.lower n
      ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩)).val
    (((Finite.ConstructedCover.CM.finiteCover (Fin n)).project
      (Finite.IntegralVacuum.CM.LowerBare.lowerLift (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hB.map _))).val) = _
  rw [Real.BareGenerators.CM.lower_projection, Finite.CoverFields.CM.projection_matrix,
    Finite.IntegralVacuum.CM.LowerBare.lowerLift_projection]
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic,
        Finite.IntegralVacuum.CM.LowerBare.lower, hij]
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic,
        Finite.IntegralVacuum.CM.LowerBare.lower, hij]

theorem operator_conjugation
    (U A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n))
    (V B : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    ProductOperators.CM.operator (U⁻¹ * A * U, V⁻¹ * B * V) =
      (ProductOperators.CM.operator (U, V))⁻¹ *
        ProductOperators.CM.operator (A, B) * ProductOperators.CM.operator (U, V) := by
  change ProductOperators.CM.operator ((U, V)⁻¹ * (A, B) * (U, V)) = _
  rw [map_mul, map_mul, map_inv]

theorem matrix_map_neg {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (B : Matrix (Fin n) (Fin n) K) : (-B).map f = -(B.map f) := by
  apply Matrix.ext
  intro i j
  exact map_neg f (B i j)

theorem finite_lower_action {I : Type*} [Fintype I] (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    Finite.BareNe.CM.Group.bareAction (Finite.IntegralVacuum.CM.LowerBare.lowerLift B hB) =
      (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := I))⁻¹ *
        Finite.Quadratic.CM.finiteQuadratic (-B) * Finite.FourierHeisenberg.CM.Equiv.fourierEquiv := rfl

theorem upper_action (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    Constructed.ConstructedAdelicGroup.CM.action n (Quadratic.CM.upper n B hB) =
      ProductOperators.CM.operator
        (Real.SchrodingerAction.CM.action n (Real.BareGenerators.CM.upper n
          ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩),
        Finite.Quadratic.CM.finiteQuadratic (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))) := by
  change AdelicPairGroup.CM.action _ _ (AdelicPairGroup.CM.assemble _ _ _) = _
  rw [AdelicPairGroup.CM.action_assemble, Finite.CoverFields.CM.action,
    Finite.QuadraticBare.CM.quadraticLift_action]
  rfl

theorem lower_action (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    Constructed.ConstructedAdelicGroup.CM.action n (lower n B hB) = (Fourier.CM.fourierEquiv n)⁻¹ *
      Constructed.ConstructedAdelicGroup.CM.action n (Quadratic.CM.upper n (-B) hB.neg) * Fourier.CM.fourierEquiv n := by
  change AdelicPairGroup.CM.action _ _ (AdelicPairGroup.CM.assemble _ _ _) = _
  rw [AdelicPairGroup.CM.action_assemble, Finite.CoverFields.CM.action, finite_lower_action]
  change ProductOperators.CM.operator
    (Real.SchrodingerAction.CM.action n (Real.BareGenerators.CM.lower n
      ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩),
    (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := Fin n))⁻¹ *
      Finite.Quadratic.CM.finiteQuadratic (-(B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf))) *
        Finite.FourierHeisenberg.CM.Equiv.fourierEquiv) = _
  rw [Real.BareGenerators.CM.lower_action, operator_conjugation, upper_action]
  simp only [matrix_map_neg]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Lower.CM
