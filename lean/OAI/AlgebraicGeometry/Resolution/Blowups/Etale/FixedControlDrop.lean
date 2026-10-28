import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialProductBound
import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicBlowupChartEtale
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Fixed Control Drop -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.FixedControlDrop.Construction

noncomputable section

/-! Fixed-control order drop on actual étale charts of intrinsic-center blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type*) {R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra.Smooth k R] [Algebra.FormallyEtale R S]

/-- An étale transform factored by a positive power of the intrinsic tangent
ideal has strictly smaller differential order at the same prescribed control. -/
theorem smooth_etale_intrinsic_product_order_drop (I J : Ideal R) (K : Ideal S)
    (n b : ℕ) (hb : 0 < b) (hcenter : I = Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hfact : J.map (algebraMap R S) = (I.map (algebraMap R S)) ^ b * K)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k K n = ⊤ := by
  have htotalK : J.map (algebraMap R S) ≤ K := by
    rw [hfact]
    exact Ideal.mul_le.mpr (fun x _ y hy => K.mul_mem_left x hy)
  have htotalIK : J.map (algebraMap R S) ≤ I.map (algebraMap R S) * K := by
    rw [hfact]
    exact Ideal.mul_mono (Ideal.pow_le_self (Nat.ne_of_gt hb)) le_rfl
  have htangent : I.map (algebraMap R S) ≤ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k K n := by
    rw [hcenter, Blowups.Smooth.DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange]
    exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k n htotalK
  have hbase : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R S)) (n + 1) = ⊤ := by
    rw [← Blowups.Smooth.DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange, hbound, Ideal.map_top]
  have h := (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k (n + 1) htotalIK).trans
    ((Global.DifferentialProductBound.Construction.relativeDifferential_mul_le_sup k (I.map (algebraMap R S)) K n).trans
      (sup_le htangent le_rfl))
  rw [hbase] at h
  exact top_le_iff.mp h

omit [Algebra R S] [IsScalarTower k R S] [Algebra.FormallyEtale R S] in
/-- The same result uses an explicit coefficient-preserving étale ring map,
so its application does not depend on an ambient choice of scalar action. -/
theorem smooth_etale_intrinsic_product_order_drop_hom (φ : R →+* S) (hφ : φ.Etale)
    (hk : ∀ x : k, φ (algebraMap k R x) = algebraMap k S x)
    (I J : Ideal R) (K : Ideal S) (n b : ℕ) (hb : 0 < b)
    (hcenter : I = Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hfact : J.map φ = (I.map φ) ^ b * K)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k K n = ⊤ := by
  let : Algebra R S := φ.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (hk x).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hφ
  exact smooth_etale_intrinsic_product_order_drop k I J K n b hb hcenter hfact hbound

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.FixedControlDrop.Construction
