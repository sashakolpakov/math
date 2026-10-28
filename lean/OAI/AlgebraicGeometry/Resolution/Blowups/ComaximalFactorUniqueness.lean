import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianIdealSheafColon

/-! # Comaximal Factor Uniqueness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ComaximalFactorUniqueness.Construction

noncomputable section

/-! A comaximal factor is uniquely determined by its product and complementary factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ideal_comaximal_product_colon {R : Type*} [CommRing R]
    (K L : Ideal R) (h : K ⊔ L = ⊤) : (K * L).colon (L : Set R) = K := by
  apply le_antisymm
  · intro a ha
    have hone : (1 : R) ∈ K ⊔ L := by rw [h]; trivial
    obtain ⟨k, hk, l, hl, he⟩ := Submodule.mem_sup.mp hone
    rw [← mul_one a, ← he, mul_add]
    exact K.add_mem (K.mul_mem_left a hk)
      (Ideal.mul_le_left (Submodule.mem_colon.mp ha l hl))
  · intro a ha
    apply Submodule.mem_colon.mpr
    intro l hl
    exact Ideal.mul_mem_mul ha hl

theorem noetherianIdealSheafColon_comaximal_factor
    {X : Scheme} [IsLocallyNoetherian X] (K L : X.IdealSheafData) (h : K ⊔ L = ⊤) :
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (K * L) L = K := by
  ext1
  funext U
  exact ideal_comaximal_product_colon (K.ideal U) (L.ideal U)
    (congrArg (fun N : X.IdealSheafData => N.ideal U) h)

theorem idealSheaf_comaximal_factor_unique
    {X : Scheme} [IsLocallyNoetherian X] (K K' L : X.IdealSheafData)
    (hK : K ⊔ L = ⊤) (hK' : K' ⊔ L = ⊤) (hprod : K * L = K' * L) : K = K' := by
  rw [← noetherianIdealSheafColon_comaximal_factor K L hK, hprod,
    noetherianIdealSheafColon_comaximal_factor K' L hK']

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ComaximalFactorUniqueness.Construction
