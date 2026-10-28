import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.OrzechProperty
import Mathlib.RingTheory.FiniteType
import Mathlib.Data.Fintype.EquivFin

/-! # Equal Rank Surjectivity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EqualRankSurjectivity.LinearAlgebra

noncomputable section

/-! Surjectivity between finite free modules of equal rank implies injectivity over a commutative ring. -/

variable {R M N I J : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Finite I] [Finite J]

theorem injective_of_surjective_of_basis_card
    (b : Module.Basis I R M) (c : Module.Basis J R N)
    (hcard : Nat.card I = Nat.card J) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Injective f := by
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  let : Module.Finite R N := Module.Finite.of_basis c
  have h : Fintype.card I = Fintype.card J := by simpa only [Nat.card_eq_fintype_card] using hcard
  let e := b.equiv c (Fintype.equivOfCardEq h)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap f e.injective hf

end

end OAI.AlgebraicGeometry.Comparison.Betti.EqualRankSurjectivity.LinearAlgebra
