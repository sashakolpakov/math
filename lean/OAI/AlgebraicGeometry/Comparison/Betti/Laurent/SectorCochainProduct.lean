import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousSectorSingle
import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochains

/-! # Sector Cochain Product -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorCochainProduct.Dolbeault

noncomputable section

/-! Reorder finite Laurent sector cochains into cochains for each fixed support. -/

open _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochains.Cech

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev homogeneousSectorCochains (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℤ) (q : ℕ) :=
  ∀ t : Fin (q + 1) → ι, HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies (Finset.univ.image t) d

abbrev homogeneousSectorSupportedCochains (d : ℤ) (q : ℕ) (J : Finset ι) :=
  ↥(SupportedCochains.Cech.supportedCechCochains ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d) J q)

def homogeneousSectorCochainProduct (d : ℤ) (q : ℕ) :
    homogeneousSectorCochains ι d q ≃+ (∀ J : Finset ι, homogeneousSectorSupportedCochains d q J) where
  toFun f J := ⟨fun t => HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficientMap (Finset.univ.image t) d J (f t),
    fun t hJ => HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficientMap_zero_of_not_subset (Finset.univ.image t) d J hJ (f t)⟩
  invFun z t := ⟨⟨fun J => ((z J).val t).val,
    ⟨fun J => ((z J).val t).property.1, fun J hJ => congrArg Subtype.val ((z J).property t hJ)⟩⟩,
    fun J => ((z J).val t).property.2⟩
  left_inv f := by
    funext t
    apply Subtype.ext
    apply Subtype.ext
    funext J
    rfl
  right_inv z := by
    funext J
    apply Subtype.ext
    funext t
    apply Subtype.ext
    rfl
  map_add' f g := by
    funext J
    apply Subtype.ext
    funext t
    rfl

theorem homogeneousSectorCochainProduct_apply (d : ℤ) (q : ℕ)
    (f : homogeneousSectorCochains ι d q) (J : Finset ι) (t : Fin (q + 1) → ι) :
    (homogeneousSectorCochainProduct d q f J).val t =
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficientMap (Finset.univ.image t) d J (f t) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorCochainProduct.Dolbeault
