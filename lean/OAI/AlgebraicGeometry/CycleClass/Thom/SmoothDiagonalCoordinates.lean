import OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalRegular
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Smooth.Flat

/-! # Smooth Diagonal Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SmoothDiagonalCoordinates.Constructions

noncomputable section

/-! Every point of a smooth algebra has a principal neighborhood
with etale polynomial coordinates. In those coordinates, the actual
diagonal ideal at every diagonal prime has a regular generating list. -/

open scoped TensorProduct
open RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalIdeal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.PolynomialDiagonalRegular.Constructions

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

theorem exists_regular_diagonal_neighborhood (p : PrimeSpectrum R) :
    ∃ f ∉ p.asIdeal, ∃ n : ℕ,
      ∃ (_ : Algebra (MvPolynomial (Fin n) k) (Localization.Away f)),
      ∃ (_ : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f)),
        Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f) ∧
        ∀ q : PrimeSpectrum (Localization.Away f),
          ∃ rs : List (Localization.AtPrime (q.asIdeal.comap
              (Algebra.TensorProduct.lmul' k).toRingHom)),
            rs.length = n ∧
            IsWeaklyRegular (Localization.AtPrime (q.asIdeal.comap
              (Algebra.TensorProduct.lmul' k).toRingHom)) rs ∧
            (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.comap
              (Algebra.TensorProduct.lmul' k).toRingHom))) ∧
            Ideal.ofList rs = (KaehlerDifferential.ideal k (Localization.Away f)).map
              (algebraMap ((Localization.Away f) ⊗[k] (Localization.Away f))
                (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' k).toRingHom))) := by
  obtain ⟨f, hf, n, a, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p.asIdeal)
  let := a
  let := ht
  let := he
  let : Module.Flat (MvPolynomial (Fin n) k) (Localization.Away f) := inferInstance
  let : IsNoetherianRing (Localization.Away f) :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin n) k) (Localization.Away f)
  let : IsNoetherianRing ((Localization.Away f) ⊗[MvPolynomial (Fin n) k] (Localization.Away f)) :=
    Algebra.FiniteType.isNoetherianRing (Localization.Away f) _
  refine ⟨f, hf, n, a, ht, he, ?_⟩
  intro q
  exact ⟨Local.PolynomialDiagonalIdeal.Constructions.localEquations k (Localization.Away f) n q,
    Local.PolynomialDiagonalRegular.Constructions.localEquations_length k (Localization.Away f) n q,
    Local.PolynomialDiagonalRegular.Constructions.localEquations_weaklyRegular k (Localization.Away f) n q,
    Local.PolynomialDiagonalRegular.Constructions.localEquations_mem_maximal k (Localization.Away f) n q,
    Local.PolynomialDiagonalIdeal.Constructions.ideal_ofList_localEquations k (Localization.Away f) n q⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SmoothDiagonalCoordinates.Constructions
