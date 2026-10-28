import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MultiplicityArithmeticTransport

/-! # Quadratic Multiplicity Basis -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticMultiplicityBasis.CM

noncomputable section

/-! The actual rational CM multiplicity basis gives an invertible
quadratic-algebra matrix. Its congruence takes the original skew form
to the diagonal form of the new orthogonal basis, with the factor 2δ. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open _root_.Module

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

abbrev basisMultiplicityCoefficients (a : Fin 2 → K) (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :=
  fun j => Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b j) (b j)

def quadraticMultiplicityBasis (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) :
    (Matrix (Fin 2) (Fin 2) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  Units.map (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm.toRingHom.mapMatrix.toMonoidHom
    (Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm))

theorem quadratic_multiplicity_basis_entry (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (i j : Fin 2) :
    (quadraticMultiplicityBasis K δ hδ hδ0 b).val i j =
      (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (b j i) := by
  change (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm ((b.equivFun.symm (Pi.single j 1)) i) = _
  have he : b.equivFun.symm (Pi.single j 1) = b j := by
    simp [Basis.equivFun_symm_apply, Pi.single_apply]
  exact congrArg (fun x => (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (x i)) he

theorem direct_source_skew_unit_diagonal [IsGalois ℚ K] (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0) :
    (BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0).val =
      Matrix.diagonal (fun j => (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (2 * δ * a j)) := by
  rw [BallArithmetic.CM.directSourceSkewUnit, CMGlobalFrames.CM.cm_skew_unit_val]
  apply congrArg Matrix.diagonal
  funext j
  apply congrArg (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm
  ring

theorem direct_source_skew_unit_conjugate_transpose [IsGalois ℚ K] (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0) :
    (BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0).val.conjTranspose =
      -(BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0).val :=
  DiagonalFrame.CM.diagonal_skew_conjugateTranspose _ _

omit δ hδ hδ0 in
theorem multiplicity_basis_cross_entry (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0)
    (i j : Fin 2) (hij : i ≠ j) : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b j) (b i) = 0 := by
  have h10 : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 1) (b 0) = 0 := by
    rw [← TransportNew.CM.multiplicity_hermitian_symm K a ha, horth, map_zero]
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact h10
  · exact horth
  · exact False.elim (hij rfl)

omit hδ hδ0 in
theorem multiplicity_basis_skew_entry (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0) (i j : Fin 2) :
    (∑ k, IsCMField.complexConj K (b i k) * (2 * δ * a k) * b j k) =
      if i = j then 2 * δ * basisMultiplicityCoefficients K a b i else 0 := by
  have he : (∑ k, IsCMField.complexConj K (b i k) * (2 * δ * a k) * b j k) =
      2 * δ * Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b j) (b i) := by
    simp only [Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  by_cases hij : i = j
  · subst j
    simp [basisMultiplicityCoefficients]
  · simp only [ite_eq_right hij, multiplicity_basis_cross_entry K a ha b horth i j hij, mul_zero]

theorem quadratic_multiplicity_basis_congruence [IsGalois ℚ K] (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (horth : Analysis.DifferentialForms.Coordinates.LocalApproximation.hermitian a (b 0) (b 1) = 0)
    (hb : ∀ j, IsCMField.complexConj K (basisMultiplicityCoefficients K a b j) = basisMultiplicityCoefficients K a b j)
    (hb0 : ∀ j, basisMultiplicityCoefficients K a b j ≠ 0) :
    (quadraticMultiplicityBasis K δ hδ hδ0 b).val.conjTranspose *
      (BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0).val * (quadraticMultiplicityBasis K δ hδ hδ0 b).val =
      (BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 (basisMultiplicityCoefficients K a b) hb hb0).val := by
  rw [direct_source_skew_unit_diagonal, direct_source_skew_unit_diagonal]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, quadratic_multiplicity_basis_entry,
    Matrix.diagonal_apply]
  apply (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).injective
  simp only [← QuadraticModel.CM.cm_quadratic_equiv_conjugation, map_sum, map_mul,
    AlgEquiv.apply_symm_apply, apply_ite, map_zero]
  have he := multiplicity_basis_skew_entry K δ a ha b horth i j
  by_cases hij : i = j
  · simpa only [ite_eq_left hij] using he
  · simpa only [ite_eq_right hij] using he

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticMultiplicityBasis.CM
