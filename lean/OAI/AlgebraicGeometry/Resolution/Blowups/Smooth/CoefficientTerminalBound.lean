import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointChartTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialLocalBound

/-! # Coefficient Terminal Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientTerminalBound.Construction

noncomputable section

/-! A terminal coefficient order bound clears the original ambient order locus. -/

variable (k : Type*) {R H : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing R] [CommRing H] [Algebra k R] [Algebra k H] [Algebra.Smooth k R]

/-- A retained coefficient ideal with a terminal factorial-control bound
clears the ambient order locus through the actual hypersurface identification.
The coefficient ideal need not itself be the unit ideal. -/
theorem retracted_coefficient_terminal_bound_clears_order
    (z : R) (J : Ideal R) (n : ℕ) (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (e : (R ⧸ Ideal.span {z}) ≃+* H) (C : Ideal (R ⧸ Ideal.span {z}))
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1))
    (hterminal : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom)
      ((n + 1).factorial - 1) = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤ := by
  by_contra hproper
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hproper
  let : M.IsMaximal := hM
  have hzM : z ∈ M := hle hz
  have horder := (ClosedWeightedOrder.Construction.closedPoint_local_order_iff J M (n + 1)).mp
    ((ClosedPointChartTransport.Construction.smooth_closedPoint_order_iff_relative_differentialIdeal k J M n).mpr hle)
  let N := M.map (Ideal.Quotient.mk (Ideal.span {z}))
  let : N.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact (Ideal.span_singleton_le_iff_mem M).mpr hzM)
  have hcoef : C ≤ N ^ (n + 1).factorial :=
    hupp.trans (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal_le_of_order k z J M (n + 1) horder)
  let Q := N.map e.toRingHom
  let : Q.IsMaximal :=
    (Ideal.isMaximal_map_iff_of_bijective e.toRingHom e.bijective (I := N)).mpr inferInstance
  have hmap : C.map e.toRingHom ≤ Q ^ (n + 1).factorial := by
    have h := Ideal.map_mono (f := e.toRingHom) hcoef
    rwa [Ideal.map_pow] at h
  have hord := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k (C.map e.toRingHom)
    ((n + 1).factorial - 1)
  rw [hterminal] at hord
  have hno := DifferentialLocalBound.Construction.local_order_lt_of_differential_top (C.map e.toRingHom)
    ((n + 1).factorial - 1) (top_le_iff.mp hord) Q
  apply hno
  rw [Nat.sub_add_cancel (Nat.factorial_pos (n + 1))]
  exact (ClosedWeightedOrder.Construction.closedPoint_local_order_iff (C.map e.toRingHom) Q (n + 1).factorial).mpr hmap

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientTerminalBound.Construction
