import OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCoefficientCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedGeneratorFamily

/-! # Zero Dimensional Coefficient Permissibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCoefficientPermissibility.Construction

noncomputable section

/-! The coefficient ideal in dimension zero lifts to a permissible ambient center. -/

variable {H : Type*} [CommRing H]

/-- Containment of a weighted coefficient ideal in a radical ideal forces
containment of every unweighted coefficient ideal. -/
theorem weightedCoefficientIdeal_component_le_radical (b : ℕ) (J : Fin b → Ideal H)
    (K : Ideal H) (hK : K.IsRadical) (hJ : WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ K) (j : Fin b) :
    J j ≤ K := by
  have hp : J j ^ WeightedCoefficientIdeal.Construction.coefficientWeight b j ≤ K := (le_iSup (fun i => J i ^ WeightedCoefficientIdeal.Construction.coefficientWeight b i) j).trans hJ
  intro x hx
  exact hK ⟨WeightedCoefficientIdeal.Construction.coefficientWeight b j, hp (Ideal.pow_mem_pow hx _)⟩

variable {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R] [Algebra ℚ R]

/-- In coefficient dimension zero, the retained coefficient ideal itself
lifts to a permissible ambient center for the original control. -/
theorem zero_dimensional_coefficient_center_permissible
    (D : Derivation k R R) (z : R) (hz : D z = 1)
    [IsNoetherianRing (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0)
    (p : ι → R) (b : ℕ) (C : Ideal (R ⧸ Ideal.span {z}))
    (hC : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C) :
    Ideal.span (Set.range p) ≤ (C.comap (Ideal.Quotient.mk (Ideal.span {z}))) ^ b := by
  let I := C.comap (Ideal.Quotient.mk (Ideal.span {z}))
  have hzI : z ∈ I := by
    change Ideal.Quotient.mk (Ideal.span {z}) z ∈ C
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)]
    exact C.zero_mem
  apply (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hz p I hzI b).mpr
  intro j hj
  have hmap : I.map (Ideal.Quotient.mk (Ideal.span {z})) = C :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective C
  have hn : b - j ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hj)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hmap, hm, ZeroDimensionalCoefficientCenter.Construction.zero_dimensional_ideal_pow hd C m]
  exact weightedCoefficientIdeal_component_le_radical b
    (fun i => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p i.val) C
    (ZeroDimensionalCoefficientCenter.Construction.zero_dimensional_ideal_isRadical hd C) hC ⟨j, hj⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCoefficientPermissibility.Construction
