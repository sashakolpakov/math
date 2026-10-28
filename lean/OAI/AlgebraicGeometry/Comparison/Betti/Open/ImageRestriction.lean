import OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardCohomology
import Mathlib.Topology.LocalAtTarget

/-! # Image Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ImageRestriction.Cech

noncomputable section

/-! Restriction to an open commutes with actual abelian direct image along the restricted continuous map. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (U : Opens Y)

def openPreimageContinuousMap : TopCat.of ((Opens.map f).obj U) ⟶ TopCat.of U :=
  TopCat.ofHom (f.hom.restrictPreimage U)

theorem openPreimageContinuousMap_closed (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (openPreimageContinuousMap f U) := by
  change Topology.IsClosedEmbedding ((U : Set Y).restrictPreimage f)
  exact Set.restrictPreimage_isClosedEmbedding (U : Set Y) hf

theorem openDirectImageRestriction_open (W : Opens U) :
    (Opens.map f).obj (U.isOpenEmbedding.functor.obj W) =
      ((Opens.map f).obj U).isOpenEmbedding.functor.obj
        ((Opens.map (openPreimageContinuousMap f U)).obj W) := by
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    have hx : f x ∈ U := hux ▸ u.property
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change (⟨f x, hx⟩ : U) ∈ W
    have he : (⟨f x, hx⟩ : U) = u := Subtype.ext hux.symm
    exact he ▸ hu
  · rintro ⟨x', hx', rfl⟩
    exact ⟨⟨f x'.val, x'.property⟩, hx', rfl⟩

def openDirectImageRestrictionIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat U.isOpenEmbedding).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) ≅
    (TopCat.Sheaf.pushforward AddCommGrpCat (openPreimageContinuousMap f U)).obj
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat ((Opens.map f).obj U).isOpenEmbedding).obj F) := by
  apply (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology U) AddCommGrpCat).preimageIso
  refine NatIso.ofComponents
    (fun W => F.obj.mapIso (eqToIso (congrArg op (openDirectImageRestriction_open f U W.unop)))) ?_
  intro W W' g
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  exact (F.obj.map_comp _ _).symm.trans
    ((congrArg F.obj.map (Subsingleton.elim _ _)).trans (F.obj.map_comp _ _))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ImageRestriction.Cech
