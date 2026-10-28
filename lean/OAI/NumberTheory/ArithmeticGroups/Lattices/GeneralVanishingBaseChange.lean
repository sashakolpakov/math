import OAI.NumberTheory.ArithmeticGroups.Lattices.ReducedFieldBaseChange
import OAI.NumberTheory.ArithmeticGroups.Lattices.SeparableCoordinateIdeal

/-! # General Vanishing Base Change -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GeneralVanishingBaseChange.Construction

noncomputable section

/-! Universal vanishing ideals of geometrically connected matrix groups
commute with every extension field in characteristic zero. -/

open scoped Classical TensorProduct

theorem prime_polynomial_ideal_charZero_extension_radical
    {k K σ : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    (I.map (MvPolynomial.map (algebraMap k K))).IsRadical := by
  let : IsReduced (K ⊗[k] (MvPolynomial σ k ⧸ I)) :=
    ReducedFieldBaseChange.Construction.field_tensor_domain_charZero_reduced k K (MvPolynomial σ k ⧸ I)
  exact SeparableCoordinateIdeal.Construction.polynomial_ideal_extension_radical_of_reduced_tensor I

theorem vanishingIdeal_charZero_baseChange
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    VanishingIdeal.Construction.coordinateVanishingIdeal (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) =
      (VanishingIdeal.Construction.coordinateVanishingIdeal G).map (MvPolynomial.map (algebraMap k K)) := by
  let : (VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime := GeometricIrreducibility.Construction.coordinateVanishingIdeal_isPrime G hG
  have hrad := prime_polynomial_ideal_charZero_extension_radical
    (K := K) (VanishingIdeal.Construction.coordinateVanishingIdeal G)
  apply le_antisymm
  · rw [CoordinateIdeal.Construction.vanishingIdeal_eq_radical_definingIdeal, ← SeparableCoordinateIdeal.Construction.affineDefiningIdeal_baseChange]
    apply hrad.radical_le_iff.mpr
    exact Ideal.map_mono (CoordinateIdeal.Construction.definingIdeal_le_vanishingIdeal G)
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    exact BaseChange.Construction.coefficient_map_mem_baseChange_vanishingIdeal G (algebraMap k K) hp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GeneralVanishingBaseChange.Construction
