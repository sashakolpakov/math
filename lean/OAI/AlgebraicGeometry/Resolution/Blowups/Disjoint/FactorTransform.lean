import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorControlledTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ColonDisjointBlowupPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.IteratedColon

/-! # Factor Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorTransform.Construction

noncomputable section

/-! Every ideal, including transverse boundary ideals, has identical controlled transforms under the disjoint-center factorization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_pow_sup_eq_top {X : Scheme} (K L : X.IdealSheafData)
    (h : K ⊔ L = ⊤) (b : ℕ) : K ^ b ⊔ L = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  have hU := congrArg (fun N : X.IdealSheafData => N.ideal U) h
  change K.ideal U ^ b ⊔ L.ideal U = ⊤
  simpa only [pow_one] using Ideal.isCoprime_iff_sup_eq.mp
    ((Ideal.isCoprime_iff_sup_eq.mpr hU).pow (m := b) (n := 1))

theorem disjointFactorBlowupIso_controlled_all
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (K L J : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥)
    (hdisjoint : K ⊔ L = ⊤) (b : ℕ) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (K * L) J (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) b).comap
      (FactorControlledTransform.Construction.disjointFactorBlowupIso K L hK hL hdisjoint).hom =
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b) (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) b := by
  let I := K * L
  have hI : I ≠ ⊥ := Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let κ := GlobalBlowup.Data.Construction.globalBlowupToBase K hK
  let L' := L.comap κ
  have hL' : L' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL
  let σ := GlobalBlowup.Data.Construction.globalBlowupToBase L' hL'
  let q := σ ≫ κ
  let e := FactorControlledTransform.Construction.disjointFactorBlowupIso K L hK hL hdisjoint
  have he : e.hom ≫ π = q := FactorControlledTransform.Construction.disjointFactorBlowupIso_over K L hK hL hdisjoint
  have hsplit : K.comap κ ⊔ L' = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_sup, hdisjoint, Scheme.IdealSheafData.comap_top]
  have hquot : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b).comap σ =
      NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap q) ((K.comap q) ^ b) := by
    change (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap κ) ((K.comap κ) ^ b)).comap σ = _
    rw [ColonDisjointBlowupPullback.Construction.noetherianIdealSheafColon_comap_disjoint_blowup _ _ L' hL'
      (idealSheaf_pow_sup_eq_top _ _ hsplit b), IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  change (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap π) ((I.comap π) ^ b)).comap e.hom =
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b).comap σ) ((L'.comap σ) ^ b)
  rw [IdealSheaf.ColonRestriction.Construction.noetherianIdealSheafColon_comap_open, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, he,
    hquot, IdealSheaf.IteratedColon.Construction.noetherianIdealSheafColon_colon]
  have hi : I.comap q = K.comap q * L'.comap σ := by
    change (K * L).comap (σ ≫ κ) = _
    rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, Scheme.IdealSheafData.comap_comp L]
  rw [hi, mul_pow]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorTransform.Construction
