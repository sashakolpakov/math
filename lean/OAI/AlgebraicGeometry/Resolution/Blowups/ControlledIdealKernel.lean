import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback

/-! # Controlled Ideal Kernel -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel.Construction

noncomputable section

/-! Controlled ideals vanish on maps avoiding the center whenever the original ideal vanishes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem idealSheaf_le_ker_iff_comap_eq_bot {V X : Scheme.{u}}
    (H : X.IdealSheafData) (j : V ⟶ X) : H ≤ j.ker ↔ H.comap j = ⊥ := by
  rw [← Scheme.IdealSheafData.map_bot j, Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff]

theorem idealSheaf_comap_eq_top_of_avoids_support {V X : Scheme.{u}}
    (I : X.IdealSheafData) (j : V ⟶ X) (h : ∀ v : V, j v ∉ I.support) : I.comap j = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro v hv
  rw [Scheme.IdealSheafData.support_comap] at hv
  exact (h v hv).elim

theorem controlledIdealSheaf_exceptional_mul_le {Y X : Scheme.{u}} [IsLocallyNoetherian Y]
    (I H : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X) :
    (I.comap π) ^ b * GlobalControlled.Ideal.Construction.controlledIdealSheaf I H b π ≤ H.comap π := by
  intro U
  apply Ideal.mul_le.mpr
  intro a ha c hc
  rw [mul_comm]
  exact Submodule.mem_colon.mp hc a ha

theorem controlledIdealSheaf_le_ker {V Y X : Scheme.{u}} [IsLocallyNoetherian Y]
    (I H : X.IdealSheafData) (b : ℕ) (π : Y ⟶ X) (j : V ⟶ Y)
    (hH : H ≤ (j ≫ π).ker) (hI : I.comap (j ≫ π) = ⊤) :
    GlobalControlled.Ideal.Construction.controlledIdealSheaf I H b π ≤ j.ker := by
  apply (idealSheaf_le_ker_iff_comap_eq_bot _ j).mpr
  have he := Scheme.IdealSheafData.comap_mono j (controlledIdealSheaf_exceptional_mul_le I H b π)
  change ((I.comap π) ^ b * GlobalControlled.Ideal.Construction.controlledIdealSheaf I H b π).comap j ≤ (H.comap π).comap j at he
  rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hI] at he
  have hz := (idealSheaf_le_ker_iff_comap_eq_bot H (j ≫ π)).mp hH
  simpa only [hz, ← Scheme.IdealSheafData.one_eq_top, one_pow, one_mul, le_bot_iff] using he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel.Construction
