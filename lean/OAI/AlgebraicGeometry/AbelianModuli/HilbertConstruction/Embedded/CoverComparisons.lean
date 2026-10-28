import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PullbackIdentity
import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # Cover Comparisons -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.CoverComparisons

noncomputable section

/-! Compare the product-based test ambients with the canonical pullback open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P T : Over S) (C : T.left.OpenCover)

/-- The ordinary pullback ambient over a member of the test cover. -/
def coverPullbackAmbient (i : C.I₀) : Over (C.X i) :=
  Over.mk (pullback.snd (FamilyFunctor.embeddedFamilyAmbient P T).hom (C.f i))

/-- The product-based ambient and canonical pullback ambient are isomorphic over the cover member. -/
def embeddedCoverIso (i : C.I₀) :
    FamilyFunctor.embeddedFamilyAmbient P (FamilyOpenCover.overOpenCoverObject T C i) ≅ coverPullbackAmbient P T C i :=
  Over.isoMk (FamilyFunctor.embeddedFamilyAmbient_isPullback P (FamilyOpenCover.overOpenCoverMap T C i)).isoPullback
    (FamilyFunctor.embeddedFamilyAmbient_isPullback P (FamilyOpenCover.overOpenCoverMap T C i)).isoPullback_hom_snd

variable [Category C.I₀] [C.LocallyDirected]

/-- Transitions in the cover are morphisms of test schemes over the original base. -/
def overOpenCoverTransition {i j : C.I₀} (f : i ⟶ j) :
    FamilyOpenCover.overOpenCoverObject T C i ⟶ FamilyOpenCover.overOpenCoverObject T C j :=
  Over.homMk (C.trans f)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ T.hom) (C.trans_map f)))

theorem overOpenCoverTransition_map {i j : C.I₀} (f : i ⟶ j) :
    overOpenCoverTransition T C f ≫ FamilyOpenCover.overOpenCoverMap T C j = FamilyOpenCover.overOpenCoverMap T C i := by
  apply Over.OverMorphism.ext
  exact C.trans_map f

/-- The comparison is natural along every transition of the directed cover. -/
theorem embeddedCoverIso_inv_transition {i j : C.I₀} (f : i ⟶ j) :
    (embeddedCoverIso P T C i).inv.left ≫ FamilyFunctor.embeddedFamilyAmbientMap P (overOpenCoverTransition T C f) =
      Scheme.Cover.trans (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom) f ≫ (embeddedCoverIso P T C j).inv.left := by
  let a := FamilyFunctor.embeddedFamilyAmbientMap P (overOpenCoverTransition T C f)
  let cᵢ := FamilyFunctor.embeddedFamilyAmbientMap P (FamilyOpenCover.overOpenCoverMap T C i)
  let cⱼ := FamilyFunctor.embeddedFamilyAmbientMap P (FamilyOpenCover.overOpenCoverMap T C j)
  let eᵢ := (embeddedCoverIso P T C i).inv.left
  let eⱼ := (embeddedCoverIso P T C j).inv.left
  let d := Scheme.Cover.trans (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom) f
  let bᵢ := (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).f i
  let bⱼ := (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom).f j
  have : IsOpenImmersion cⱼ := MorphismProperty.of_isPullback
    (FamilyFunctor.embeddedFamilyAmbient_isPullback P (FamilyOpenCover.overOpenCoverMap T C j)).flip (C.map_prop j)
  have hi : eᵢ ≫ cᵢ = bᵢ :=
    (FamilyFunctor.embeddedFamilyAmbient_isPullback P (FamilyOpenCover.overOpenCoverMap T C i)).isoPullback_inv_fst
  have hj : eⱼ ≫ cⱼ = bⱼ :=
    (FamilyFunctor.embeddedFamilyAmbient_isPullback P (FamilyOpenCover.overOpenCoverMap T C j)).isoPullback_inv_fst
  have hd : d ≫ bⱼ = bᵢ := Scheme.Cover.trans_map (C.pullback₁ (FamilyFunctor.embeddedFamilyAmbient P T).hom) f
  have ha : a ≫ cⱼ = cᵢ :=
    (PullbackIdentity.embeddedFamilyAmbientMap_comp P (overOpenCoverTransition T C f) (FamilyOpenCover.overOpenCoverMap T C j)).symm.trans
      (congrArg (FamilyFunctor.embeddedFamilyAmbientMap P) (overOpenCoverTransition_map T C f))
  change eᵢ ≫ a = d ≫ eⱼ
  apply (cancel_mono cⱼ).mp
  exact ((Category.assoc _ _ _).trans ((congrArg (fun z => eᵢ ≫ z) ha).trans hi)).trans
    (((Category.assoc _ _ _).trans ((congrArg (fun z => d ≫ z) hj).trans hd)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.CoverComparisons
