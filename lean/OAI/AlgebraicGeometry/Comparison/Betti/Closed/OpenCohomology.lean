import OAI.AlgebraicGeometry.Comparison.Betti.Open.ImageRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage
import OAI.AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison

/-! # Open Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.OpenCohomology.Cech

noncomputable section

/-! Closed direct image identifies cohomology on every inverse-image open and transfers Čech-intersection acyclicity. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)

def closedPushforwardOpenCohomologyEquiv (U : Opens Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    Sheaf.H.{0} (J := Opens.grothendieckTopology U)
      (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F))) n ≃
    Sheaf.H.{0} (J := Opens.grothendieckTopology ((Opens.map f).obj U))
      (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf
        ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat ((Opens.map f).obj U).isOpenEmbedding).obj F)) n :=
  ((Sheaf.functorH.{0} (Opens.grothendieckTopology U) n).mapIso
    (Open.ImageRestriction.Cech.openDirectImageRestrictionIso f U F)).addCommGroupIsoToAddEquiv.toEquiv.trans
      (PushforwardCohomology.Cech.closedPushforwardCohomologyEquiv (Open.ImageRestriction.Cech.openPreimageContinuousMap f U)
        (Open.ImageRestriction.Cech.openPreimageContinuousMap_closed f U hf).isInducing
        (Open.ImageRestriction.Cech.openPreimageContinuousMap_closed f U hf).isClosed_range
        ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat ((Opens.map f).obj U).isOpenEmbedding).obj F) n).toEquiv

include hf in
theorem closedSource_cechIntersectionsAcyclic {ι : Type} (U : ι → Opens Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hF : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F)) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (fun i => (Opens.map f).obj (U i)) F := by
  intro p t q
  change Subsingleton (Sheaf.H.{0} ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat
    (∏ᶜ fun k : Fin (p + 1) => (Opens.map f).obj (U (t k))).isOpenEmbedding).obj F) (q + 1))
  rw [← AdditiveCechImage.additiveCechIntersection_preimage f U p t]
  let e := closedPushforwardOpenCohomologyEquiv f hf (∏ᶜ fun k : Fin (p + 1) => U (t k)) F (q + 1)
  exact ⟨fun a b => e.symm.injective ((hF p t q).elim _ _)⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.OpenCohomology.Cech
