import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.FunctorialMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealCancellation
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IdealSheafProducts

/-! # Map Controlled Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapControlledIdeal.Construction

noncomputable section

/-! Exact transport of permissible controlled ideals through global blowup comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

theorem globalBlowupMap_totalIdeal (q : Y ⟶ X) (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) :
    (J.comap (Data.Construction.globalBlowupToBase I hI)).comap (FunctorialMap.Construction.globalBlowupMap q I hI hY) =
      (J.comap q).comap (Data.Construction.globalBlowupToBase (I.comap q) hY) := by
  rw [← Scheme.IdealSheafData.comap_comp, FunctorialMap.Construction.globalBlowupMap_over,
    Scheme.IdealSheafData.comap_comp]

/-- Permissible controlled transforms commute exactly with the actual global
comparison, including comparisons from closed carriers. -/
theorem globalBlowupMap_controlledIdeal (q : Y ⟶ X) (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (hY : I.comap q ≠ ⊥) (b : ℕ) (hp : J ≤ I ^ b) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (FunctorialMap.Construction.globalBlowupMap q I hI hY) =
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (I.comap q) (J.comap q) hY b := by
  have hpY : J.comap q ≤ (I.comap q) ^ b := by
    have h := Scheme.IdealSheafData.comap_mono q hp
    change J.comap q ≤ (I ^ b).comap q at h
    rwa [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow] at h
  apply Locally.PrincipalIdealCancellation.Construction.locallyPrincipal_idealSheaf_mul_left_injective
    (((I.comap q).comap (Data.Construction.globalBlowupToBase (I.comap q) hY)) ^ b)
    (Integral.IdealSheafProducts.Construction.idealSheaf_pow_ne_bot _ (Nonzero.Construction.globalBlowup_totalIdeal_ne_bot _ _ hY hY) b)
    ((Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal (I.comap q) hY).pow b)
  have h := congrArg (fun K : (Data.Construction.globalBlowup I hI).IdealSheafData =>
      K.comap (FunctorialMap.Construction.globalBlowupMap q I hI hY))
    (GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization I J hI b hp)
  rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, globalBlowupMap_totalIdeal,
    globalBlowupMap_totalIdeal] at h
  exact h.trans (GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization (I.comap q) (J.comap q) hY b hpY).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapControlledIdeal.Construction
