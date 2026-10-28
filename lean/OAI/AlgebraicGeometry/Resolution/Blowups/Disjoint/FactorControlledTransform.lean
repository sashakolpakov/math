import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBlowupIso
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealCancellation
import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.CenterPermissibility

/-! # Factor Controlled Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorControlledTransform.Construction

noncomputable section

/-! The actual disjoint-factor blowup isomorphism preserves fixed-control transforms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

def disjointFactorBlowupIso (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥)
    (hdisjoint : K ⊔ L = ⊤) :
    FactorBlowupIso.Construction.disjointFactorBlowup K L hK hL ≅ GlobalBlowup.Data.Construction.globalBlowup (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) :=
  (FactorBlowupIso.Construction.exists_disjointFactorBlowup_iso K L hK hL hdisjoint).choose

theorem disjointFactorBlowupIso_over (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥)
    (hdisjoint : K ⊔ L = ⊤) :
    (disjointFactorBlowupIso K L hK hL hdisjoint).hom ≫
      GlobalBlowup.Data.Construction.globalBlowupToBase (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) =
      FactorBlowupIso.Construction.disjointFactorBlowupToBase K L hK hL :=
  (FactorBlowupIso.Construction.exists_disjointFactorBlowup_iso K L hK hL hdisjoint).choose_spec

theorem disjointFactorBlowupIso_controlled
    (K L J : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥)
    (hdisjoint : K ⊔ L = ⊤) (b : ℕ) (hp : J ≤ (K * L) ^ b) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (K * L) J (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) b).comap
      (disjointFactorBlowupIso K L hK hL hdisjoint).hom =
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
  let e := disjointFactorBlowupIso K L hK hL hdisjoint
  have he : e.hom ≫ π = q := disjointFactorBlowupIso_over K L hK hL hdisjoint
  have hKp : J ≤ K ^ b := hp.trans (pow_le_pow_left' (show K * L ≤ K from fun U => Ideal.mul_le_left) b)
  have hLp : J ≤ L ^ b := hp.trans (pow_le_pow_left' (show K * L ≤ L from fun U => Ideal.mul_le_right) b)
  let J₁ := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b
  let J₂ := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal L' J₁ hL' b
  have h₂p : J₁ ≤ L' ^ b := CenterPermissibility.Construction.globalBlowup_preserves_disjoint_center_permissibility K L J hK b b
    (by rwa [sup_comm]) hLp
  have hIq : I.comap q ≠ ⊥ := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot L' (I.comap κ) hL'
      (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K I hK hI)
  have hIqp : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap q) := by
    have h := (Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal I hI).comap e.hom
    rw [← Scheme.IdealSheafData.comap_comp, he] at h
    exact h
  apply Locally.PrincipalIdealCancellation.Construction.locallyPrincipal_idealSheaf_mul_left_injective ((I.comap q) ^ b)
    (Integral.IdealSheafProducts.Construction.idealSheaf_pow_ne_bot _ hIq b) (hIqp.pow b)
  have hleft : (I.comap q) ^ b * (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap e.hom = J.comap q := by
    have h := congrArg (fun N => N.comap e.hom) (GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization I J hI b hp)
    rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, he] at h
    exact h
  have hright : (I.comap q) ^ b * J₂ = J.comap q := by
    have h₁ := congrArg (fun N => N.comap σ) (GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization K J hK b hKp)
    rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp] at h₁
    have h₂ := GlobalControlled.Factorization.Construction.globalBlowup_controlledIdeal_factorization L' J₁ hL' b h₂p
    have hi : I.comap q = K.comap q * L'.comap σ := by
      change (K * L).comap (σ ≫ κ) = _
      rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, Scheme.IdealSheafData.comap_comp L]
    rw [hi, mul_pow, mul_assoc, h₂]
    exact h₁
  exact hleft.trans hright.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorControlledTransform.Construction
