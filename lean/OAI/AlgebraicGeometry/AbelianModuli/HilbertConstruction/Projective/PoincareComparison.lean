import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RelativePicardInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.RepresentingIsoPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointNormalization

/-! # Poincare Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Canonical representing dual comparisons preserve actual normalized Poincare bundles on arbitrary tests when the original abelian scheme has a projective presentation over a locally noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

theorem Dual.Data.DualAbelianData.uniqueUnderlyingIso_poincareAt_iso (D E : Dual.Data.DualAbelianData A)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) {T : Over S} (f : T ⟶ D.abelian.scheme) :
    Nonempty ((D.poincareAt f).sheaf ≅ (E.poincareAt (f ≫ (D.uniqueUnderlyingIso E).hom)).sheaf) := by
  apply Projective.RelativePicardInjectivity.projective_bundleIso_of_relativePicard_eq A.scheme P η[A.scheme].left η[A.scheme].w T
    (D.poincareAt f) (E.poincareAt (f ≫ (D.uniqueUnderlyingIso E).hom))
    (A.familyZeroSection T) (A.familyZeroSection_fst T)
    (D.poincareAt_zeroIso f ≪≫ (E.poincareAt_zeroIso (f ≫ (D.uniqueUnderlyingIso E).hom)).symm)
  rw [← D.pointRelativeClass_eq_poincare, ← E.pointRelativeClass_eq_poincare,
    D.uniqueUnderlyingIso_hom_classifies E]

theorem Dual.Data.DualAbelianData.uniqueUnderlyingIso_poincare_iso (D E : Dual.Data.DualAbelianData A)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :
    Nonempty (D.poincare.sheaf ≅ (E.poincareAt (D.uniqueUnderlyingIso E).hom).sheaf) := by
  have h := D.uniqueUnderlyingIso_poincareAt_iso E P (𝟙 D.abelian.scheme)
  rw [Category.id_comp] at h
  let e : (D.poincareAt (𝟙 D.abelian.scheme)).sheaf ≅ D.poincare.sheaf :=
    (Scheme.Modules.pullbackCongr ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map_id D.abelian.scheme)).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackId _).app D.poincare.sheaf
  exact ⟨e.symm ≪≫ h.some⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
