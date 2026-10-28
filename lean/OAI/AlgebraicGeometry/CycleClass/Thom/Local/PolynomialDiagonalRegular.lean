import OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalIdeal
import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialTensorRegularSequence
import Mathlib.Data.List.FinRange

/-! # Polynomial Diagonal Regular -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalRegular.Constructions

noncomputable section

/-! Flat unramified polynomial coordinates give an actual regular
sequence generating the diagonal ideal in each diagonal local ring. -/

open scoped TensorProduct
open RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalIdeal.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (n : ℕ)
  [Algebra (MvPolynomial (Fin n) k) R] [IsScalarTower k (MvPolynomial (Fin n) k) R]

omit [IsScalarTower k (MvPolynomial (Fin n) k) R] in
theorem localEquations_length (q : PrimeSpectrum R) : (PolynomialDiagonalIdeal.Constructions.localEquations k R n q).length = n :=
  List.length_ofFn

omit [IsScalarTower k (MvPolynomial (Fin n) k) R] in
theorem localEquations_mem_maximal (q : PrimeSpectrum R) :
    ∀ r ∈ PolynomialDiagonalIdeal.Constructions.localEquations k R n q, r ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom)) := by
  intro r hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))
    (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom) _).mpr
  change Algebra.TensorProduct.lmul' k
    (Tensor.BalanceIdeal.Constructions.difference k (MvPolynomial (Fin n) k) R (MvPolynomial.X i)) ∈ q.asIdeal
  simp only [Tensor.BalanceIdeal.Constructions.difference, map_sub, Algebra.TensorProduct.lmul'_apply_tmul, mul_one, one_mul, sub_self]
  exact q.asIdeal.zero_mem

variable [Module.Flat (MvPolynomial (Fin n) k) R]

theorem localEquations_weaklyRegular (q : PrimeSpectrum R) :
    IsWeaklyRegular
      (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))
      (PolynomialDiagonalIdeal.Constructions.localEquations k R n q) := by
  have h := PolynomialTensorRegularSequence.Constructions.difference_weaklyRegular k R
    (List.ofFn (id : Fin n → Fin n)) (List.nodup_ofFn.mpr Function.injective_id)
  have hl := h.of_isLocalization
    (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))
    (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom).primeCompl
  simpa only [List.map_ofFn, Function.comp_def, id_eq, PolynomialDiagonalIdeal.Constructions.localEquations] using hl

variable [Algebra.FormallyUnramified (MvPolynomial (Fin n) k) R]
  [IsNoetherianRing (R ⊗[MvPolynomial (Fin n) k] R)]

theorem diagonal_regular_equations (q : PrimeSpectrum R) :
    IsWeaklyRegular
        (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))
        (PolynomialDiagonalIdeal.Constructions.localEquations k R n q) ∧
      Ideal.ofList (PolynomialDiagonalIdeal.Constructions.localEquations k R n q) =
        (KaehlerDifferential.ideal k R).map
          (algebraMap (R ⊗[k] R)
            (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))) :=
  ⟨localEquations_weaklyRegular k R n q, PolynomialDiagonalIdeal.Constructions.ideal_ofList_localEquations k R n q⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalRegular.Constructions
