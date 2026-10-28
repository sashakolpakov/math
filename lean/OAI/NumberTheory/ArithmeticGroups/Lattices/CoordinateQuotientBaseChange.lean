import OAI.NumberTheory.ArithmeticGroups.Lattices.GeneralVanishingBaseChange

/-! # Coordinate Quotient Base Change -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateQuotientBaseChange.Construction

noncomputable section

/-! An explicit quotient-ring description of the extended coordinate
algebra. -/

open scoped Classical TensorProduct

def polynomialQuotientBaseChangeEquiv
    {k K σ : Type*} [Field k] [Field K] [Algebra k K] (I : Ideal (MvPolynomial σ k)) :
    K ⊗[k] (MvPolynomial σ k ⧸ I) ≃+*
      MvPolynomial σ K ⧸ I.map (MvPolynomial.map (algebraMap k K)) := by
  let P := MvPolynomial σ k
  let f : P →ₐ[k] K ⊗[k] P := Algebra.TensorProduct.includeRight
  let J := I.map f
  let e : K ⊗[k] P ≃ₐ[K] MvPolynomial σ K := MvPolynomial.algebraTensorAlgEquiv k K
  have he : e.toRingHom.comp f.toRingHom = MvPolynomial.map (algebraMap k K) := by
    apply RingHom.ext
    intro p
    exact (MvPolynomial.algebraTensorAlgEquiv_tmul k K 1 p).trans (one_smul K _)
  have hJ : J.map e.toRingHom = I.map (MvPolynomial.map (algebraMap k K)) := by
    change (I.map f.toRingHom).map e.toRingHom = _
    rw [Ideal.map_map, he]
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := k) K P K I
  let e2 := Ideal.quotientEquiv J (I.map (MvPolynomial.map (algebraMap k K))) e.toRingEquiv hJ.symm
  exact e1.toRingEquiv.trans e2

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateQuotientBaseChange.Construction
