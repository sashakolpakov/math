import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.RelativePicardInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.RepresentingIsoPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointNormalization

/-! # Changed Polarized Poincare Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical dual comparisons preserve actual Poincare bundles on all base changes of a polarized locally Noetherian family. The projective and normalization arguments are constructed from the original polarization. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

variable {S T : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.baseChanged_uniqueDualIso_poincareAt_iso
    (D E : Dual.Data.DualAbelianData (A.pullback f).abelian) {U : Over T} (p : U ⟶ D.abelian.scheme) :
    Nonempty ((D.poincareAt p).sheaf ≅ (E.poincareAt (p ≫ (D.uniqueUnderlyingIso E).hom)).sheaf) := by
  apply A.baseChanged_bundleIso_of_relativePicard_eq f U
    (D.poincareAt p) (E.poincareAt (p ≫ (D.uniqueUnderlyingIso E).hom))
    ((A.pullback f).abelian.familyZeroSection U) ((A.pullback f).abelian.familyZeroSection_fst U)
    (D.poincareAt_zeroIso p ≪≫ (E.poincareAt_zeroIso (p ≫ (D.uniqueUnderlyingIso E).hom)).symm)
  rw [← D.pointRelativeClass_eq_poincare, ← E.pointRelativeClass_eq_poincare,
    D.uniqueUnderlyingIso_hom_classifies E]

theorem PolarizationData.PolarizedAbelianWithFullLevel.baseChanged_uniqueDualIso_poincare_iso
    (D E : Dual.Data.DualAbelianData (A.pullback f).abelian) :
    Nonempty (D.poincare.sheaf ≅ (E.poincareAt (D.uniqueUnderlyingIso E).hom).sheaf) := by
  have h := A.baseChanged_uniqueDualIso_poincareAt_iso f D E (𝟙 D.abelian.scheme)
  rw [Category.id_comp] at h
  let e : (D.poincareAt (𝟙 D.abelian.scheme)).sheaf ≅ D.poincare.sheaf :=
    (Scheme.Modules.pullbackCongr ((Picard.PicardSheaf.familySchemeFunctor (A.pullback f).abelian.scheme).map_id D.abelian.scheme)).app
      D.poincare.sheaf ≪≫ (Scheme.Modules.pullbackId _).app D.poincare.sheaf
  exact ⟨e.symm ≪≫ h.some⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
