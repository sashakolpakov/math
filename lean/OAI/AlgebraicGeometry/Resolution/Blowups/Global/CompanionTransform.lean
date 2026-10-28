import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Companion Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionTransform.Construction

noncomputable section

/-! Exact native companion and residual-factor identities on actual global blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ideal_comap_sup_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : Function.Bijective g) (I J : Ideal S) :
    (I ⊔ J).comap g = I.comap g ⊔ J.comap g := by
  let e := RingEquiv.ofBijective g hg
  change (I ⊔ J).comap e = I.comap e ⊔ J.comap e
  rw [← Ideal.map_symm e, Ideal.map_sup, Ideal.map_symm e, Ideal.map_symm e]

theorem affineQuotientKernel_sup {R : Type u} [CommRing R] (I J : Ideal R) :
    Affine.QuotientKernel.Construction.affineQuotientKernel (I ⊔ J) = Affine.QuotientKernel.Construction.affineQuotientKernel I ⊔ Affine.QuotientKernel.Construction.affineQuotientKernel J := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop]
  change (I ⊔ J).comap (Scheme.ΓSpecIso (.of R)).hom.hom =
    (Affine.QuotientKernel.Construction.affineQuotientKernel I).ideal ⟨⊤, isAffineOpen_top _⟩ ⊔
      (Affine.QuotientKernel.Construction.affineQuotientKernel J).ideal ⟨⊤, isAffineOpen_top _⟩
  rw [Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop, Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop]
  exact ideal_comap_sup_of_bijective _ (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.bijective I J

theorem affineQuotientKernel_markedIntersection {R : Type u} [CommRing R]
    (J L : Ideal R) (b c : ℕ) :
    Affine.QuotientKernel.Construction.affineQuotientKernel (MarkedIdealIntersection.Construction.markedIdealIntersection J L b c) =
      CompanionIdeal.Construction.globalMarkedIntersection (Affine.QuotientKernel.Construction.affineQuotientKernel J) (Affine.QuotientKernel.Construction.affineQuotientKernel L) b c := by
  rw [MarkedIdealIntersection.Construction.markedIdealIntersection, CompanionIdeal.Construction.globalMarkedIntersection, affineQuotientKernel_sup,
    Affine.QuotientKernel.Construction.affineQuotientKernel_pow, Affine.QuotientKernel.Construction.affineQuotientKernel_pow]

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem globalBlowup_markedIntersection_transform_on_chart
    (I J L : X.IdealSheafData) (hI : I ≠ ⊥) (b c : ℕ) (hJ : J ≤ I ^ b) (hL : L ≤ I ^ c)
    (U : X.affineOpens) (a : I.ideal U) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (CompanionIdeal.Construction.globalMarkedIntersection J L b c) hI (b * c)).comap
      (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) =
    (CompanionIdeal.Construction.globalMarkedIntersection (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI c) b c).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) := by
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, CompanionIdeal.Construction.globalMarkedIntersection_comap,
    GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart,
    ← affineQuotientKernel_markedIntersection]
  apply congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
  exact MarkedIdealIntersection.Construction.blowup_markedIdealIntersection_controlledTransform (I.ideal U) (J.ideal U) (L.ideal U) a b c (hJ U) (hL U)

theorem globalBlowup_markedIntersection_transform
    (I J L : X.IdealSheafData) (hI : I ≠ ⊥) (b c : ℕ) (hJ : J ≤ I ^ b) (hL : L ≤ I ^ c) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (CompanionIdeal.Construction.globalMarkedIntersection J L b c) hI (b * c) =
      CompanionIdeal.Construction.globalMarkedIntersection (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI c) b c :=
  IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (GlobalControlled.Chart.Construction.globalBlowupReesAffineCover I hI).openCover
    (fun p => globalBlowup_markedIntersection_transform_on_chart I J L hI b c hJ hL p.1 p.2)

theorem globalBlowup_companion_transform
    (I J M : X.IdealSheafData) (hI : I ≠ ⊥) (m b : ℕ)
    (hJ : J ≤ I ^ m) (hM : M ≤ I ^ (b - m)) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (CompanionIdeal.Construction.globalCompanionIdeal J M m b) hI (m * (b - m)) =
      CompanionIdeal.Construction.globalCompanionIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m)) m b :=
  globalBlowup_markedIntersection_transform I J M hI m (b - m) hJ hM

def globalResidualBoundaryFactorTransform (I M : X.IdealSheafData) (hI : I ≠ ⊥) (m b : ℕ) :
    (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData :=
  (I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ (m - b) * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m)

theorem globalResidualBoundaryFactorTransform_of_le
    (I M : X.IdealSheafData) (hI : I ≠ ⊥) (m b : ℕ) (hmb : m ≤ b) :
    globalResidualBoundaryFactorTransform I M hI m b = GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m) := by
  rw [globalResidualBoundaryFactorTransform, Nat.sub_eq_zero_of_le hmb, pow_zero, one_mul]

theorem globalResidualBoundaryFactorTransform_comap_chart
    (I M : X.IdealSheafData) (hI : I ≠ ⊥) (m b : ℕ) (U : X.affineOpens) (a : I.ideal U) :
    (globalResidualBoundaryFactorTransform I M hI m b).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (ResidualCoefficientTransform.Construction.residualBoundaryFactorTransform (I.ideal U) (M.ideal U) a m b) := by
  rw [globalResidualBoundaryFactorTransform, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow,
    GlobalControlled.Factorization.Construction.totalIdeal_comap_globalBlowupReesChart, GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart,
    ← Affine.QuotientKernel.Construction.affineQuotientKernel_pow, ← IdealSheaf.ProductRestriction.Construction.affineQuotientKernel_mul, ExceptionalIdeal.Construction.blowupChart_extendedIdeal,
    Ideal.span_singleton_pow]
  rfl

theorem globalBlowup_residual_product_transform_on_chart
    (I M J : X.IdealSheafData) (hI : I ≠ ⊥) (m b : ℕ)
    (hM : M ≤ I ^ (b - m)) (hJ : J ≤ I ^ m) (U : X.affineOpens) (a : I.ideal U) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (M * J) hI b).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) =
      (globalResidualBoundaryFactorTransform I M hI m b * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m).comap
        (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) := by
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul,
    globalResidualBoundaryFactorTransform_comap_chart, GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart,
    ← IdealSheaf.ProductRestriction.Construction.affineQuotientKernel_mul]
  apply congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
  exact ResidualCoefficientTransform.Construction.residual_boundary_product_controlledTransform (I.ideal U) (M.ideal U) (J.ideal U) a m b (hM U) (hJ U)

theorem globalBlowup_residual_product_transform
    (I M J : X.IdealSheafData) (hI : I ≠ ⊥) (m b : ℕ)
    (hM : M ≤ I ^ (b - m)) (hJ : J ≤ I ^ m) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (M * J) hI b =
      globalResidualBoundaryFactorTransform I M hI m b * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m :=
  IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (GlobalControlled.Chart.Construction.globalBlowupReesAffineCover I hI).openCover
    (fun p => globalBlowup_residual_product_transform_on_chart I M J hI m b hM hJ p.1 p.2)

theorem globalBlowup_companion_product_transform
    (I M J : X.IdealSheafData) (hI : I ≠ ⊥) (m b : ℕ) (hmb : m ≤ b)
    (hM : M ≤ I ^ (b - m)) (hJ : J ≤ I ^ m) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (M * J) hI b =
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m) * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m := by
  rw [globalBlowup_residual_product_transform I M J hI m b hM hJ,
    globalResidualBoundaryFactorTransform_of_le I M hI m b hmb]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionTransform.Construction
