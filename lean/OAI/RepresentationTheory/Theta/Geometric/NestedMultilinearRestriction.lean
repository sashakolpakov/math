import OAI.RepresentationTheory.Theta.Geometric.PowerRestrictionCongruence
import OAI.RepresentationTheory.Theta.Geometric.FrameGlobalIsoRestriction

/-! # Nested Multilinear Restriction -/

namespace OAI.RepresentationTheory.Theta.Geometric.NestedMultilinearRestriction

noncomputable section

/-! The native nested-open comparison transports the universal multilinear map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem multilinear_nestedRestriction {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    {L P : X.Modules} {n : ℕ} (β : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P) :
    ((β.restrict U.ι).restrict (X.homOfLE h)).precomp (AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nestedRestrictionIso h L).hom =
      (β.restrict V.ι).postcomp (AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nestedRestrictionIso h P).hom := by
  unfold AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nestedRestrictionIso
  simp only [Iso.trans_hom]
  rw [← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp, MultilinearRestrictionComposition.multilinear_restrict_comp,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, PowerRestrictionCongruence.multilinear_restrict_congr,
    ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp]

end

end OAI.RepresentationTheory.Theta.Geometric.NestedMultilinearRestriction
