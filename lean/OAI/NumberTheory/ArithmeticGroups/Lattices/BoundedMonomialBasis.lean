import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.Polynomial

/-! # Bounded Monomial Basis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedMonomialBasis.Construction

noncomputable section

/-! A coefficient-independent finite monomial basis for the bounded
polynomial representation. -/

open scoped Classical
open _root_.MvPolynomial

abbrev BoundedMonomials (n d : ℕ) :=
  ↥({m : (Fin n × Fin n) →₀ ℕ | m.sum (fun _ e => e) ≤ d} : Set ((Fin n × Fin n) →₀ ℕ))

instance boundedMonomialsFinite (n d : ℕ) : Finite (BoundedMonomials n d) := by
  let b : Module.Basis (BoundedMonomials n d) ℚ (BoundedRepresentation.Construction.BoundedPolynomials ℚ n d) :=
    MvPolynomial.basisRestrictSupport ℚ _
  exact Module.Finite.finite_basis b

instance boundedMonomialsFintype (n d : ℕ) : Fintype (BoundedMonomials n d) := Fintype.ofFinite _

abbrev boundedMonomialCount (n d : ℕ) := Fintype.card (BoundedMonomials n d)

def boundedMonomialBasisRaw (k : Type) [Field k] (n d : ℕ) :
    Module.Basis (BoundedMonomials n d) k (BoundedRepresentation.Construction.BoundedPolynomials k n d) :=
  MvPolynomial.basisRestrictSupport k _

theorem boundedMonomialBasisRaw_val (k : Type) [Field k] (n d : ℕ)
    (m : BoundedMonomials n d) :
    (boundedMonomialBasisRaw k n d m).val = MvPolynomial.monomial m.val 1 := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := k) _).symm (Finsupp.single m (1 : k))).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

def boundedMonomialBasis (k : Type) [Field k] (n d : ℕ) :
    Module.Basis (Fin (boundedMonomialCount n d)) k (BoundedRepresentation.Construction.BoundedPolynomials k n d) :=
  (boundedMonomialBasisRaw k n d).reindex (Fintype.equivFin (BoundedMonomials n d))

theorem boundedMonomialBasis_val (k : Type) [Field k] (n d : ℕ)
    (i : Fin (boundedMonomialCount n d)) :
    (boundedMonomialBasis k n d i).val =
      MvPolynomial.monomial ((Fintype.equivFin (BoundedMonomials n d)).symm i).val 1 := by
  rw [boundedMonomialBasis, Module.Basis.reindex_apply, boundedMonomialBasisRaw_val]

theorem boundedMonomialBasis_coefficient_map
    {k K : Type} [Field k] [Field K] [Algebra k K] (n d : ℕ)
    (i : Fin (boundedMonomialCount n d)) :
    Lattices.Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (boundedMonomialBasis k n d i) =
      boundedMonomialBasis K n d i := by
  apply Subtype.ext
  change MvPolynomial.map (algebraMap k K) (boundedMonomialBasis k n d i).val = _
  rw [boundedMonomialBasis_val, boundedMonomialBasis_val]
  simp

theorem boundedMonomialBasis_repr_coefficient_map
    {k K : Type} [Field k] [Field K] [Algebra k K] {n d : ℕ}
    (p : BoundedRepresentation.Construction.BoundedPolynomials k n d) (i : Fin (boundedMonomialCount n d)) :
    (boundedMonomialBasis K n d).repr (Lattices.Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) p) i =
      algebraMap k K ((boundedMonomialBasis k n d).repr p i) := by
  let f : BoundedRepresentation.Construction.BoundedPolynomials k n d →ₗ[k] BoundedRepresentation.Construction.BoundedPolynomials K n d :=
    Integral.Polynomial.Construction.boundedIntegralCoefficientMap n d
  have he : ((boundedMonomialBasis K n d).repr.toLinearMap.restrictScalars k).comp f =
      (Finsupp.mapRange.linearMap (Algebra.linearMap k K)).comp
        (boundedMonomialBasis k n d).repr.toLinearMap := by
    apply (boundedMonomialBasis k n d).ext
    intro j
    change (boundedMonomialBasis K n d).repr
      (Lattices.Finite.UniformExteriorLine.Construction.boundedCoefficientMap (K := K) (boundedMonomialBasis k n d j)) = _
    rw [boundedMonomialBasis_coefficient_map]
    simp
  exact congrArg (fun a => a i) (LinearMap.congr_fun he p)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedMonomialBasis.Construction
