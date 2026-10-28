import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Local
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalComaximalFactors
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ExceptionalPrincipality
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.IdealSheafProducts

/-! # Factor Blowup Iso -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBlowupIso.Construction

noncomputable section

/-! Blowing up a product of two comaximal centers is the actual succession of their blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

abbrev disjointFactorBlowup (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) : Scheme :=
  GlobalBlowup.Data.Construction.globalBlowup (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)) (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL)

def disjointFactorBlowupToBase (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) :
    disjointFactorBlowup K L hK hL ⟶ X :=
  GlobalBlowup.Data.Construction.globalBlowupToBase (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)) (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) ≫
    GlobalBlowup.Data.Construction.globalBlowupToBase K hK

theorem exists_disjointFactorBlowup_iso
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hdisjoint : K ⊔ L = ⊤) :
    ∃ e : disjointFactorBlowup K L hK hL ≅ GlobalBlowup.Data.Construction.globalBlowup (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL),
      e.hom ≫ GlobalBlowup.Data.Construction.globalBlowupToBase (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) =
        disjointFactorBlowupToBase K L hK hL := by
  let I := K * L
  have hI : I ≠ ⊥ := Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
  let κ := GlobalBlowup.Data.Construction.globalBlowupToBase K hK
  let L' := L.comap κ
  have hL' : L' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL
  let σ := GlobalBlowup.Data.Construction.globalBlowupToBase L' hL'
  let q := σ ≫ κ
  have hKI : K.comap π ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I K hI hK
  have hLI : L.comap π ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I L hI hL
  have hsplit : K.comap π ⊔ L.comap π = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_sup, hdisjoint, Scheme.IdealSheafData.comap_top]
  have hprod : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (K.comap π * L.comap π) := by
    rw [← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul]
    exact Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal I hI
  have hkp := hprod.comaximal_left_factor (K.comap π) (L.comap π) hsplit
  have hlp : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (L.comap π) :=
    Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.comaximal_left_factor (L.comap π) (K.comap π)
      (by rwa [sup_comm]) (by rwa [mul_comm])
  let a := GlobalBlowup.Local.Construction.globalBlowupUniversalLift K hK π hKI hkp
  have ha : a ≫ κ = π := GlobalBlowup.Local.Construction.globalBlowupUniversalLift_over K hK π hKI hkp
  have hLa : L'.comap a = L.comap π := by rw [← Scheme.IdealSheafData.comap_comp, ha]
  have hLa0 : L'.comap a ≠ ⊥ := hLa.symm ▸ hLI
  have hLap : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (L'.comap a) := hLa.symm ▸ hlp
  let c := GlobalBlowup.Local.Construction.globalBlowupUniversalLift L' hL' a hLa0 hLap
  have hc : c ≫ σ = a := GlobalBlowup.Local.Construction.globalBlowupUniversalLift_over L' hL' a hLa0 hLap
  have hIq : I.comap q ≠ ⊥ := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot L' (I.comap κ) hL'
      (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K I hK hI)
  have hIqp : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf (I.comap q) := by
    change Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf ((K * L).comap (σ ≫ κ))
    rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact ((Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal K hK).comap σ).mul
      (Global.ExceptionalPrincipality.Construction.globalBlowup_center_locallyPrincipal L' hL')
  let d := GlobalBlowup.Local.Construction.globalBlowupUniversalLift I hI q hIq hIqp
  have hd : d ≫ π = q := GlobalBlowup.Local.Construction.globalBlowupUniversalLift_over I hI q hIq hIqp
  have hcd : c ≫ d = 𝟙 (GlobalBlowup.Data.Construction.globalBlowup I hI) := by
    apply GlobalBlowup.Local.Construction.globalBlowup_hom_ext I hI π (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I I hI hI)
    · rw [Category.assoc, hd, ← Category.assoc, hc, ha]
    · exact Category.id_comp _
  have hda : d ≫ a = σ := by
    apply GlobalBlowup.Local.Construction.globalBlowup_hom_ext K hK q
      (by
        rw [Scheme.IdealSheafData.comap_comp]
        exact GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot L' (K.comap κ) hL'
          (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K K hK hK))
    · rw [Category.assoc, ha, hd]
    · rfl
  have hdc : d ≫ c = 𝟙 (GlobalBlowup.Data.Construction.globalBlowup L' hL') := by
    apply GlobalBlowup.Local.Construction.globalBlowup_hom_ext L' hL' σ (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot L' L' hL' hL')
    · rw [Category.assoc, hc, hda]
    · exact Category.id_comp _
  exact ⟨⟨d, c, hdc, hcd⟩, hd⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBlowupIso.Construction
