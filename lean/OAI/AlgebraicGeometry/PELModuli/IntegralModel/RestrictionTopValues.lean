import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame

/-! # Restriction Top Values -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictionTopValues

noncomputable section

/-! Native restriction maps on top sections agree with the corresponding
ambient-open module maps and the actual structure-sheaf coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalAffineFrame
universe u
variable {X : Scheme.{u}} {M N : X.Modules}

theorem restrictionTopIso_naturality (U : X.Opens) (q : M ⟶ N)
    (x : Γ(M.restrict U.ι, ⊤)) :
    (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso N U).hom (((Scheme.Modules.restrictFunctor U.ι).map q).app ⊤ x) =
      q.app U ((SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom x) := by
  change N.presheaf.map (eqToHom U.ι_image_top.symm).op
      (q.val.app (op (U.ι ''ᵁ ⊤)) x) =
    q.val.app (op U) (M.presheaf.map (eqToHom U.ι_image_top.symm).op x)
  exact (PresheafOfModules.naturality_apply q.val (eqToHom U.ι_image_top.symm).op x).symm

theorem restrictionTopIso_unit (U : X.Opens) (r : Γ(U.toScheme, ⊤)) :
    (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U).hom
      ((Scheme.Modules.restrictUnitIso U.ι).inv.app ⊤ r) = U.topIso.hom r := by
  change X.presheaf.map (eqToHom U.ι_image_top.symm).op ((U.ι.appIso ⊤).inv r) = _
  rw [Scheme.Opens.ι_appIso, Scheme.Opens.topIso_hom]
  rfl

theorem restrictSection_top_value (U : X.Opens) (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (r : Γ(U.toScheme, ⊤)) :
    (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom ((AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q).app ⊤ r) = q.app U (U.topIso.hom r) := by
  change (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom
    (((Scheme.Modules.restrictFunctor U.ι).map q).app ⊤
      ((Scheme.Modules.restrictUnitIso U.ι).inv.app ⊤ r)) = _
  rw [restrictionTopIso_naturality, restrictionTopIso_unit]

theorem restrictSection_top_zero_iff (U : X.Opens) (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (r : Γ(U.toScheme, ⊤)) :
    (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q).app ⊤ r = 0 ↔ q.app U (U.topIso.hom r) = 0 := by
  rw [← restrictSection_top_value]
  exact (map_eq_zero_iff (ConcreteCategory.hom (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom)
    (ConcreteCategory.bijective_of_isIso (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom).injective).symm

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictionTopValues
