import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedParameterDimension
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Order Dimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.OrderDimension

noncomputable section

/-! A nonzero finite principal colength in a Noetherian local
domain forces the ring to have dimension exactly one. -/

theorem dimension (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (r : R) (hr : r ≠ 0) (hn : (Ring.ord R r).toNat ≠ 0) : ringKrullDim R = 1 := by
  have hfin : Ring.ord R r ≠ ⊤ := by
    intro he
    exact hn (by rw [he, ENat.toNat_top])
  have hpos : Ring.ord R r ≠ 0 := by
    intro he
    exact hn (by rw [he, ENat.toNat_zero])
  have hrm : r ∈ IsLocalRing.maximalIdeal R := by
    by_contra h
    exact hpos (Ring.ord_of_isUnit (IsLocalRing.notMem_maximalIdeal.mp h))
  let Q := R ⧸ Ideal.span {r}
  have hfinite : IsFiniteLength R Q := Module.length_ne_top_iff.mp hfin
  let : IsArtinian R Q := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2
  let : IsArtinianRing Q := isArtinian_of_tower R (inferInstanceAs (IsArtinian R Q))
  let : Nontrivial Q := Module.length_pos_iff.mp (pos_iff_ne_zero.mpr hpos)
  have hQ : ringKrullDim Q = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
      (isArtinianRing_iff_krullDimLE_zero.mp (inferInstanceAs (IsArtinianRing Q)))
  have he := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (IsSMulRegular.of_ne_zero hr) hrm
  rw [hQ, zero_add] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.OrderDimension
