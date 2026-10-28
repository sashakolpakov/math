import OAI.RepresentationTheory.Theta.Geometric.NonvanishingScalarPullback
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneLocalSection

/-! # Section Frame Nonvanishing -/

namespace OAI.RepresentationTheory.Theta.Geometric.SectionFrameNonvanishing

noncomputable section

/-! Native affine frame coordinates describe the exact nonvanishing open. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem sectionFrame_endValue {X : Scheme} {M : X.Modules}
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.1.toScheme) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U.1.toScheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.1.ι s ≫ e.hom) =
      AlgebraicGeometry.SheafCohomology.Projective.FrameSections.localTrivializationTopSection M U e (s.app ⊤ (1 : Γ(X, ⊤))) := by
  have hu : AlgebraicGeometry.SheafCohomology.Projective.FrameSections.localTrivializationRestriction (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U (1 : Γ(X, ⊤)) =
      (Scheme.Modules.restrictUnitIso U.1.ι).inv.app ⊤ (1 : Γ(U.1.toScheme, ⊤)) := by
    change X.presheaf.map (eqToHom U.1.ι_image_top).op
      (X.presheaf.map (homOfLE le_top).op (1 : Γ(X, ⊤))) = (U.1.ι.appIso ⊤).inv 1
    simp only [map_one]
  have hm := AlgebraicGeometry.SheafCohomology.Projective.FrameSections.localTrivializationRestriction_map s U (1 : Γ(X, ⊤))
  rw [hu] at hm
  exact (congrArg (fun v => e.hom.app ⊤ v) hm).symm

theorem sectionNonvanishing_in_frame {X : Scheme} {M : X.Modules}
    (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.1.toScheme) :
    U.1.ι ⁻¹ᵁ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = U.1.toScheme.basicOpen
      (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.localTrivializationTopSection M U e (s.app ⊤ (1 : Γ(X, ⊤)))) := by
  rw [← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction.sectionNonvanishing_restrictSection U.1.ι s,
    ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.1.ι s) e,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar, sectionFrame_endValue]

end

end OAI.RepresentationTheory.Theta.Geometric.SectionFrameNonvanishing
