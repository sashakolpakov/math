import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianIdealSheafColon

/-! # Iterated Colon -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.IteratedColon.Construction

noncomputable section

/-! Iterated ideal quotients equal quotient by the product of denominator ideals. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ideal_le_colon_iff_mul_le {R : Type*} [CommRing R] (A B K : Ideal R) :
    B ≤ A.colon (K : Set R) ↔ B * K ≤ A := by
  constructor
  · intro h
    apply Ideal.mul_le.mpr
    intro x hx y hy
    exact Submodule.mem_colon.mp (h hx) y hy
  · intro h x hx
    apply Submodule.mem_colon.mpr
    intro y hy
    exact h (Ideal.mul_mem_mul hx hy)

theorem ideal_colon_colon_eq_colon_mul {R : Type*} [CommRing R] (A K L : Ideal R) :
    (A.colon (K : Set R)).colon (L : Set R) = A.colon ((K * L : Ideal R) : Set R) := by
  apply le_antisymm
  · apply (ideal_le_colon_iff_mul_le _ _ _).mpr
    have h₁ := (ideal_le_colon_iff_mul_le (A.colon (K : Set R))
      ((A.colon (K : Set R)).colon (L : Set R)) L).mp le_rfl
    have h₂ := (ideal_le_colon_iff_mul_le A (A.colon (K : Set R)) K).mp le_rfl
    calc
      (A.colon (K : Set R)).colon (L : Set R) * (K * L) =
          ((A.colon (K : Set R)).colon (L : Set R) * L) * K := by ac_rfl
      _ ≤ A.colon (K : Set R) * K := Ideal.mul_mono h₁ le_rfl
      _ ≤ A := h₂
  · apply (ideal_le_colon_iff_mul_le _ _ _).mpr
    apply (ideal_le_colon_iff_mul_le _ _ _).mpr
    rw [mul_assoc, mul_comm L K]
    exact (ideal_le_colon_iff_mul_le A (A.colon ((K * L : Ideal R) : Set R)) (K * L)).mp le_rfl

theorem noetherianIdealSheafColon_colon {X : Scheme} [IsLocallyNoetherian X]
    (A K L : X.IdealSheafData) :
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A K) L =
      NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A (K * L) := by
  apply Scheme.IdealSheafData.ext
  funext U
  exact ideal_colon_colon_eq_colon_mul (A.ideal U) (K.ideal U) (L.ideal U)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.IteratedColon.Construction
