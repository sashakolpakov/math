import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Chart
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing

/-! # Factorization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization.Construction

noncomputable section

/-! Exact global factorization of the total transform on the actual blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affine_controlled_kernel_factorization {R : Type u} [CommRing R]
    (I J : Ideal R) (b : ℕ) (a : I) (hperm : J ≤ I ^ b) :
    (Affine.QuotientKernel.Construction.affineQuotientKernel (I.map (Blowup.Charts.Construction.blowupChartConstants I a))) ^ b *
      Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform I J b a) =
        Affine.QuotientKernel.Construction.affineQuotientKernel (J.map (Blowup.Charts.Construction.blowupChartConstants I a)) := by
  rw [← Affine.QuotientKernel.Construction.affineQuotientKernel_pow, ← IdealSheaf.ProductRestriction.Construction.affineQuotientKernel_mul]
  apply congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
  rw [ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.span_singleton_pow]
  exact ControlledTransform.Construction.blowup_controlledTransform_factorization I J b a hperm

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem totalIdeal_comap_globalBlowupReesChart (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (U : X.affineOpens) (a : I.ideal U) :
    (J.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).comap (Chart.Construction.globalBlowupReesChart I hI U a) =
      Affine.QuotientKernel.Construction.affineQuotientKernel ((J.ideal U).map (Blowup.Charts.Construction.blowupChartConstants (I.ideal U) a)) := by
  rw [← Scheme.IdealSheafData.comap_comp, Chart.Construction.globalBlowupReesChart_over,
    Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel]

theorem globalBlowup_controlledIdeal_factorization_on_chart (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (hperm : J ≤ I ^ b) (U : X.affineOpens) (a : I.ideal U) :
    ((I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b *
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap (Chart.Construction.globalBlowupReesChart I hI U a) =
        (J.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).comap (Chart.Construction.globalBlowupReesChart I hI U a) := by
  rw [IdealSheaf.ProductRestriction.Construction.idealSheaf_comap_mul_open, IdealSheaf.ColonRestriction.Construction.idealSheaf_comap_pow_open,
    Chart.Construction.globalBlowupControlledIdeal_comap_reesChart,
    totalIdeal_comap_globalBlowupReesChart, totalIdeal_comap_globalBlowupReesChart]
  exact affine_controlled_kernel_factorization (I.ideal U) (J.ideal U) b a (hperm U)

/-- A permissible center gives an exact factorization of the native total
transform by the exceptional ideal power and the native controlled ideal. -/
theorem globalBlowup_controlledIdeal_factorization (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (b : ℕ) (hperm : J ≤ I ^ b) :
    (I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)) ^ b * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b =
      J.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) := by
  exact IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (Chart.Construction.globalBlowupReesAffineCover I hI).openCover
    (fun p => globalBlowup_controlledIdeal_factorization_on_chart I J hI b hperm p.1 p.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Factorization.Construction
