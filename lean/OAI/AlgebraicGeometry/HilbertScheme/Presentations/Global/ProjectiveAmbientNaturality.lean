import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectiveAmbient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientProjections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialNaturality

/-! # Projective Ambient Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectiveAmbientNaturality.GradedHilbert

noncomputable section

/-! The common relative projective ambient and the native families transported
to it commute with arbitrary changes of test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ} {T U : Over S} (a : U ⟶ T) (x : T ⟶ M)

theorem globalProjectiveAmbientIso_naturality :
    Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Intrinsic.PolynomialNaturality.GradedHilbert.nativePolynomialTestMap M a x) ≫
        (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M x).hom =
      (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M (a ≫ x)).hom ≫ Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).hom_ext
  · change (_ ≫ _) ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      (_ ≫ _) ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T
    simp only [Category.assoc, ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso_projection, Hilbert.AmbientProjections.ambientMap_projection]
    rw [← Category.assoc, ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso_projection]
    rfl
  · change (_ ≫ _) ≫ (prod.snd : T ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      (_ ≫ _) ≫ (prod.snd : T ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left
    simp only [Category.assoc, ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso_projective,
      Hilbert.AmbientProjections.ambientMap_second, Hilbert.AmbientProjections.ambientMap_second_assoc]

theorem globalProjectiveAmbientIso_inverse_naturality :
    (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M (a ≫ x)).inv ≫
        Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Intrinsic.PolynomialNaturality.GradedHilbert.nativePolynomialTestMap M a x) =
      Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a ≫ (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M x).inv := by
  apply (cancel_mono (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M x).hom).mp
  rw [Category.assoc, globalProjectiveAmbientIso_naturality, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem polynomialFamilyOverOriginalBase_baseChange
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left)) :
    ProjectiveAmbient.GradedHilbert.polynomialFamilyOverOriginalBase M (a ≫ x)
        (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Intrinsic.PolynomialNaturality.GradedHilbert.nativePolynomialTestMap M a x) F) =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a (ProjectiveAmbient.GradedHilbert.polynomialFamilyOverOriginalBase M x F) := by
  apply Subtype.ext
  change (F.val.comap (Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Intrinsic.PolynomialNaturality.GradedHilbert.nativePolynomialTestMap M a x))).comap
      (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M (a ≫ x)).inv =
    (F.val.comap (ProjectiveAmbient.GradedHilbert.globalProjectiveAmbientIso M x).inv).comap (Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    globalProjectiveAmbientIso_inverse_naturality]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectiveAmbientNaturality.GradedHilbert
