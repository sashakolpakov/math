import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DualCenterPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CenterQuotient
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ColonRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedGeneratorFamily

/-! # Frame Center Permissibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.FrameCenterPermissibility.Construction

noncomputable section

/-! Exact permissible smooth lifts of coefficient coordinate families in any dimension. -/

universe u

variable (k : Type u) {H R ι : Type u} {τ : Type*}
  [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra.Smooth k H] [Algebra ℚ R] [Fintype ι] [DecidableEq ι]

/-- A retained coefficient ideal with a permissible dual-coordinate center
lifts through the actual hypersurface retraction to a smooth ambient center
permissible at the original control. This applies in every coefficient dimension. -/
theorem retracted_frame_coefficient_center_permissible
    (D : Derivation k R R) (z : R) (hD : D z = 1)
    (e : (R ⧸ Ideal.span {z}) ≃ₐ[H] H) (p : τ → R) (b : ℕ)
    (g : ι → H) (δ : ι → Derivation k H H)
    (hδ : ∀ i j, δ i (g j) = if i = j then 1 else 0)
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hC : C.map e.toRingHom ≤ (Ideal.span (Set.range g)) ^ b.factorial) :
    let K := Ideal.span (Set.range g)
    let I := K.map (algebraMap H R) ⊔ Ideal.span {z}
    Ideal.span (Set.range p) ≤ I ^ b ∧ Algebra.Smooth k (R ⧸ I) := by
  let : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  let K := Ideal.span (Set.range g)
  let I := K.map (algebraMap H R) ⊔ Ideal.span {z}
  let q := Ideal.Quotient.mk (Ideal.span {z})
  have hzI : z ∈ I := (show Ideal.span {z} ≤ I from le_sup_right) (Ideal.mem_span_singleton_self z)
  have hI : I.map q = K.comap e.toRingHom := by
    change (K.map (algebraMap H R) ⊔ Ideal.span {z}).map q = _
    rw [HypersurfaceCenters.Construction.retracted_hypersurface_center_comap z e K, ← Ideal.comap_comap]
    exact Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective _
  have hweighted : WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b
      (fun j => (HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val).map e.toRingHom) ≤ K ^ b.factorial := by
    rw [← WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
    exact (Ideal.map_mono hlow).trans hC
  have hcomponents := (Blowups.Smooth.DualCenterPowerRoot.Construction.smooth_dual_center_weighted_iff k g δ hδ b
    (fun j => (HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val).map e.toRingHom)).mp hweighted
  have hperm : Ideal.span (Set.range p) ≤ I ^ b := by
    apply (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hD p I hzI b).mpr
    intro j hj
    have h := (Ideal.map_le_iff_le_comap).mp (hcomponents ⟨j, hj⟩)
    rw [IdealSheaf.ColonRestriction.Construction.ideal_comap_pow_of_bijective e.toRingHom e.bijective, ← hI] at h
    exact h
  let : Algebra.Smooth k (H ⧸ K) := DualFrameCenterSmooth.Construction.dual_derivation_family_center_smooth g δ hδ
  obtain ⟨E, _⟩ := CenterQuotient.Construction.exists_retracted_center_quotient_equiv z e K
  exact ⟨hperm, Algebra.Smooth.of_equiv (E.restrictScalars k).symm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.FrameCenterPermissibility.Construction
