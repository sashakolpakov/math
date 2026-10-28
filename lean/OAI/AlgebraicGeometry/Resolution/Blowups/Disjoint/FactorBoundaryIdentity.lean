import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryTransform

/-! # Factor Boundary Identity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundaryIdentity.Construction

noncomputable section

/-! A disjoint-center factorization splits the original exceptional boundary label into two disjoint labels and preserves every older label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupControlledIdeal_disjoint
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (C K : X.IdealSheafData) (hC : C ≠ ⊥) (b : ℕ) (hdisjoint : K ⊔ C = ⊤) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C K hC b = K.comap (GlobalBlowup.Data.Construction.globalBlowupToBase C hC) := by
  let π := GlobalBlowup.Data.Construction.globalBlowupToBase C hC
  have hs : K.comap π ⊔ C.comap π = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_sup, hdisjoint, Scheme.IdealSheafData.comap_top]
  apply Scheme.IdealSheafData.ext
  funext U
  have hU := congrArg (fun N => N.ideal U) hs
  change ((K.comap π).ideal U).colon ((((C.comap π).ideal U) ^ b : Ideal Γ(GlobalBlowup.Data.Construction.globalBlowup C hC, U)) : Set Γ(GlobalBlowup.Data.Construction.globalBlowup C hC, U)) = _
  simpa only [pow_one] using CenterPermissibility.Construction.ideal_power_colon_eq_of_sup_top ((K.comap π).ideal U)
    ((C.comap π).ideal U) 1 b hU

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

def disjointFactorBlowupBoundary (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥)
    {β : Type} (D : β → X.IdealSheafData) :
    Option (Option β) → (FactorBlowupIso.Construction.disjointFactorBlowup K L hK hL).IdealSheafData :=
  CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
    (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK D)

theorem disjointFactorBlowupBoundary_old_label
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    {β : Type} (D : β → X.IdealSheafData) (l : β) :
    (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) D (some l)).comap
      (FactorControlledTransform.Construction.disjointFactorBlowupIso K L hK hL hdisjoint).hom =
      disjointFactorBlowupBoundary K L hK hL D (some (some l)) :=
  FactorTransform.Construction.disjointFactorBlowupIso_controlled_all K L (D l) hK hL hdisjoint 1

theorem disjointFactorBlowupBoundary_first_exceptional
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    {β : Type} (D : β → X.IdealSheafData) :
    disjointFactorBlowupBoundary K L hK hL D (some none) =
      K.comap (FactorBlowupIso.Construction.disjointFactorBlowupToBase K L hK hL) := by
  have hs : K.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK) ⊔ L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_sup, hdisjoint, Scheme.IdealSheafData.comap_top]
  change GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK))
    (K.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)) (GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot K L hK hL) 1 = _
  rw [globalBlowupControlledIdeal_disjoint _ _ _ 1 hs]
  exact (Scheme.IdealSheafData.comap_comp K _ _).symm

theorem disjointFactorBlowupBoundary_exceptional_product
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    {β : Type} (D : β → X.IdealSheafData) :
    (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (K * L) (Integral.IdealSheafProducts.Construction.idealSheaf_mul_ne_bot K L hK hL) D none).comap
      (FactorControlledTransform.Construction.disjointFactorBlowupIso K L hK hL hdisjoint).hom =
      disjointFactorBlowupBoundary K L hK hL D (some none) *
        disjointFactorBlowupBoundary K L hK hL D none := by
  change ((K * L).comap (GlobalBlowup.Data.Construction.globalBlowupToBase (K * L) _)).comap _ = _
  rw [← Scheme.IdealSheafData.comap_comp, FactorControlledTransform.Construction.disjointFactorBlowupIso_over, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul,
    disjointFactorBlowupBoundary_first_exceptional K L hK hL hdisjoint D]
  exact congrArg (fun N => K.comap (FactorBlowupIso.Construction.disjointFactorBlowupToBase K L hK hL) * N)
    (Scheme.IdealSheafData.comap_comp L _ _)

theorem disjointFactorBlowupBoundary_exceptionals_disjoint
    (K L : X.IdealSheafData) (hK : K ≠ ⊥) (hL : L ≠ ⊥) (hdisjoint : K ⊔ L = ⊤)
    {β : Type} (D : β → X.IdealSheafData) :
    disjointFactorBlowupBoundary K L hK hL D (some none) ⊔
      disjointFactorBlowupBoundary K L hK hL D none = ⊤ := by
  rw [disjointFactorBlowupBoundary_first_exceptional K L hK hL hdisjoint D]
  change K.comap (FactorBlowupIso.Construction.disjointFactorBlowupToBase K L hK hL) ⊔
    (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)).comap (GlobalBlowup.Data.Construction.globalBlowupToBase _ _) = ⊤
  rw [← Scheme.IdealSheafData.comap_comp]
  change K.comap (FactorBlowupIso.Construction.disjointFactorBlowupToBase K L hK hL) ⊔
    L.comap (FactorBlowupIso.Construction.disjointFactorBlowupToBase K L hK hL) = ⊤
  rw [← Scheme.IdealSheafData.comap_sup, hdisjoint, Scheme.IdealSheafData.comap_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorBoundaryIdentity.Construction
