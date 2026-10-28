import OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility
import OAI.NumberTheory.ArithmeticGroups.Lattices.BaseChange

/-! # Separable Coordinate Ideal -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SeparableCoordinateIdeal.Construction

noncomputable section

section

/-! Prime polynomial ideals remain radical under separable algebraic
field extension. -/

open scoped Classical TensorProduct

theorem polynomial_ideal_extension_radical_of_reduced_tensor
    {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (I : Ideal (MvPolynomial σ k)) [IsReduced (K ⊗[k] (MvPolynomial σ k ⧸ I))] :
    (I.map (MvPolynomial.map (algebraMap k K))).IsRadical := by
  let P := MvPolynomial σ k
  let f : P →ₐ[k] K ⊗[k] P := Algebra.TensorProduct.includeRight
  let J := I.map f
  let e : K ⊗[k] P ≃ₐ[K] MvPolynomial σ K := MvPolynomial.algebraTensorAlgEquiv k K
  have he : e.toRingHom.comp f.toRingHom = MvPolynomial.map (algebraMap k K) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = MvPolynomial.map (algebraMap k K) p
    exact (MvPolynomial.algebraTensorAlgEquiv_tmul k K 1 p).trans (one_smul K _)
  have hJ : J.map e.toRingHom = I.map (MvPolynomial.map (algebraMap k K)) := by
    change (I.map f.toRingHom).map e.toRingHom = _
    rw [Ideal.map_map, he]
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := k) K P K I
  let e2 := Ideal.quotientEquiv J (I.map (MvPolynomial.map (algebraMap k K))) e.toRingEquiv hJ.symm
  let E := e1.toRingEquiv.trans e2
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact isReduced_of_injective E.symm E.symm.injective

theorem prime_polynomial_ideal_separable_extension_radical
    {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    (I.map (MvPolynomial.map (algebraMap k K))).IsRadical := by
  let : IsReduced (K ⊗[k] (MvPolynomial σ k ⧸ I)) :=
    GeometricIrreducibility.Construction.separable_tensor_domain_reduced k K (MvPolynomial σ k ⧸ I)
  exact polynomial_ideal_extension_radical_of_reduced_tensor I

end

/-! The universal vanishing ideal commutes with separable algebraic
field extension for geometrically connected matrix groups. -/

open scoped Classical
open _root_.MvPolynomial Set

theorem coefficient_map_determinantEquation
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K) :
    MvPolynomial.map ι (CoordinateIdeal.Construction.determinantEquation k n) = CoordinateIdeal.Construction.determinantEquation K n := by
  let Xk : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)
  have hX : (MvPolynomial.map ι).mapMatrix Xk =
      (fun i j : Fin n => (X (i, j) : Algebraic.CoordinatePolynomial n K)) := by
    ext i j : 1
    change MvPolynomial.map ι (X (i, j)) = X (i, j)
    simp
  change MvPolynomial.map ι (Xk.det - 1) = _
  rw [map_sub, map_one, (MvPolynomial.map ι).map_det, hX]
  rfl

theorem affineDefiningIdeal_baseChange
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K) :
    (CoordinateIdeal.Construction.affineDefiningIdeal G).map (MvPolynomial.map ι) =
      CoordinateIdeal.Construction.affineDefiningIdeal (BaseChange.Construction.matrixGroupBaseChange G ι) := by
  rw [CoordinateIdeal.Construction.affineDefiningIdeal, Ideal.map_span, image_insert_eq, coefficient_map_determinantEquation]
  rfl

theorem vanishingIdeal_separable_baseChange
    {k K : Type} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    VanishingIdeal.Construction.coordinateVanishingIdeal (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) =
      (VanishingIdeal.Construction.coordinateVanishingIdeal G).map (MvPolynomial.map (algebraMap k K)) := by
  let : (VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime := GeometricIrreducibility.Construction.coordinateVanishingIdeal_isPrime G hG
  have hrad := prime_polynomial_ideal_separable_extension_radical
    (K := K) (VanishingIdeal.Construction.coordinateVanishingIdeal G)
  apply le_antisymm
  · rw [CoordinateIdeal.Construction.vanishingIdeal_eq_radical_definingIdeal, ← affineDefiningIdeal_baseChange]
    apply hrad.radical_le_iff.mpr
    exact Ideal.map_mono (CoordinateIdeal.Construction.definingIdeal_le_vanishingIdeal G)
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    exact BaseChange.Construction.coefficient_map_mem_baseChange_vanishingIdeal G (algebraMap k K) hp

theorem vanishingIdeal_algebraicClosure_baseChange
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    VanishingIdeal.Construction.coordinateVanishingIdeal (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))) =
      (VanishingIdeal.Construction.coordinateVanishingIdeal G).map (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) :=
  vanishingIdeal_separable_baseChange G hG

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SeparableCoordinateIdeal.Construction
