import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.TestPicardBundleIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.RepresentingIsoPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointNormalization

/-! # Canonical Dual Poincare -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CanonicalDualPoincare

noncomputable section

/-! Canonical comparisons of any chosen duals preserve actual Poincare
bundles on arbitrary tests of a fixed Noetherian projective abelian family. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (T : Over S)
variable (D E : Dual.Data.DualAbelianData (A.pullback T.hom))

include PA

theorem universalCanonicalDual_poincareAt_iso {V : Over T.left} (f : V ⟶ D.abelian.scheme) :
    Nonempty ((D.poincareAt f).sheaf ≅ (E.poincareAt (f ≫ (D.uniqueUnderlyingIso E).hom)).sheaf) := by
  apply TestPicardBundleIso.universalTest_bundleIso_of_relativePicard_eq A PA T.hom V
    (D.poincareAt f) (E.poincareAt (f ≫ (D.uniqueUnderlyingIso E).hom))
    ((A.pullback T.hom).familyZeroSection V) ((A.pullback T.hom).familyZeroSection_fst V)
    (D.poincareAt_zeroIso f ≪≫ (E.poincareAt_zeroIso (f ≫ (D.uniqueUnderlyingIso E).hom)).symm)
  rw [← D.pointRelativeClass_eq_poincare, ← E.pointRelativeClass_eq_poincare,
    D.uniqueUnderlyingIso_hom_classifies E]

theorem universalCanonicalDual_poincare_iso :
    Nonempty (D.poincare.sheaf ≅ (E.poincareAt (D.uniqueUnderlyingIso E).hom).sheaf) := by
  have h := universalCanonicalDual_poincareAt_iso A PA T D E (𝟙 D.abelian.scheme)
  rw [Category.id_comp] at h
  let e : (D.poincareAt (𝟙 D.abelian.scheme)).sheaf ≅ D.poincare.sheaf :=
    (Scheme.Modules.pullbackCongr ((Picard.PicardSheaf.familySchemeFunctor (A.pullback T.hom).scheme).map_id D.abelian.scheme)).app
      D.poincare.sheaf ≪≫ (Scheme.Modules.pullbackId _).app D.poincare.sheaf
  exact ⟨e.symm ≪≫ h.some⟩

theorem universalCanonicalDual_poincare_class :
    Line.Bundles.LineBundle.pullbackClass ((D.uniqueUnderlyingIso E).hom ⊗ₘ 𝟙 (A.pullback T.hom).scheme).left
      (Line.Bundles.LineBundle.classOf E.poincare) = Line.Bundles.LineBundle.classOf D.poincare := by
  rw [tensorHom_id]
  change Line.Bundles.LineBundle.classOf (E.poincareAt (D.uniqueUnderlyingIso E).hom) = Line.Bundles.LineBundle.classOf D.poincare
  exact Quotient.sound ⟨(universalCanonicalDual_poincare_iso A PA T D E).some.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CanonicalDualPoincare
