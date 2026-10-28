import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FieldLineSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Field Base Coefficients -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldBaseCoefficients

noncomputable section

/-! Compare field fibers with the global coefficient spectrum used by
Presentations, retaining the actual structural maps and their section dimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u

theorem fieldBaseCoefficients_cartesian {S : Scheme.{u}} [IsAffine S]
    (X : Over S) {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    IsPullback (pullback.fst X.hom a) (pullback.snd X.hom a)
      (X.hom ≫ S.toSpecΓ) (Spec.map (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a)) := by
  rw [AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients_spec]
  exact (IsPullback.of_hasPullback X.hom a).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso S.toSpecΓ)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (Category.id_comp _).symm (Category.id_comp _).symm

theorem fieldBaseCoefficients_lineSections_finrank
    {k K : Type u} [Field k] [Field K]
    (X : Over (Spec (.of k))) [IsSeparated X.hom] [QuasiCompact X.hom]
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (a : Spec (.of K) ⟶ Spec (.of k)) :
    Module.finrank Γ(Spec (.of K), ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (pullback.snd X.hom a)).obj
        (P.pullback (pullback.fst X.hom a)).sheaf) =
      Module.finrank Γ(Spec (.of Γ(Spec (.of k), ⊤)), ⊤)
        ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (X.hom ≫ (Spec (.of k)).toSpecΓ)).obj P.sheaf) := by
  have hR : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  let := hR.toField
  exact Cartesian.FieldLineSections.PolarizationEmbedding.fieldLineSections_cartesian_finrank (X.hom ≫ (Spec (.of k)).toSpecΓ)
    P.sheaf P.locallyTrivial (pullback.fst X.hom a) (pullback.snd X.hom a)
    (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a).hom (fieldBaseCoefficients_cartesian X a)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldBaseCoefficients
