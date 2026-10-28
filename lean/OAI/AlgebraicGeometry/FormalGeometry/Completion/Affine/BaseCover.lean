import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.Glued
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.OpenCover

/-! # Base Cover -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseCover.Construction

noncomputable section

/-!
# Completion: the affine base cover pulled back to an actual site object

The two projections and the directed transitions are actual morphisms in
the original site. Their equations are the ordinary scheme pullback equations.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (W : X.ProEt)

/-- The affine open cover of the base pulled back to a site object. -/
def affineBaseCover : W.left.OpenCover := X.directedAffineCover.pullback₁ W.hom

instance : Category (affineBaseCover W).I₀ :=
  inferInstanceAs (Category X.directedAffineCover.I₀)

instance : Scheme.Cover.LocallyDirected (affineBaseCover W) :=
  Scheme.Cover.locallyDirectedPullbackCover X.directedAffineCover W.hom

/-- A member of the pulled-back affine base cover in the actual site. -/
def affineBaseCoverObject (i : X.directedAffineCover.I₀) : X.ProEt :=
  ProEtale.OpenCover.Construction.proEtaleOpenCoverObject W (affineBaseCover W) i

/-- Its projection to the original site object. -/
def affineBaseCoverProjection (i : X.directedAffineCover.I₀) : affineBaseCoverObject W i ⟶ W :=
  ProEtale.OpenCover.Construction.proEtaleOpenCoverMap W (affineBaseCover W) i

/-- Its projection to the affine object of the base. -/
def affineBaseCoverToOpen (i : X.directedAffineCover.I₀) :
    affineBaseCoverObject W i ⟶ (FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i :=
  MorphismProperty.Over.homMk (pullback.snd W.hom (X.directedAffineCover.f i))
    pullback.condition.symm

/-- A member regarded in the slice over its affine base open. -/
def affineBaseCoverSlice (i : X.directedAffineCover.I₀) :
    Over ((FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) := Over.mk (affineBaseCoverToOpen W i)

/-- The directed transition between members of the pulled-back cover. -/
def affineBaseCoverTransition {i j : X.directedAffineCover.I₀} (h : i ⟶ j) :
    affineBaseCoverObject W i ⟶ affineBaseCoverObject W j :=
  MorphismProperty.Over.homMk ((affineBaseCover W).trans h) (by
    change (affineBaseCover W).trans h ≫ (affineBaseCover W).f j ≫ W.hom =
      (affineBaseCover W).f i ≫ W.hom
    rw [← Category.assoc, Scheme.Cover.trans_map])

theorem affineBaseCoverTransition_projection {i j : X.directedAffineCover.I₀} (h : i ⟶ j) :
    affineBaseCoverTransition W h ≫ affineBaseCoverProjection W j = affineBaseCoverProjection W i :=
  MorphismProperty.Over.Hom.ext ((affineBaseCover W).trans_map h)

theorem affineBaseCoverTransition_open {i j : X.directedAffineCover.I₀} (h : i ⟶ j) :
    affineBaseCoverTransition W h ≫ affineBaseCoverToOpen W j =
      affineBaseCoverToOpen W i ≫ (FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).map h := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.map W.hom (X.directedAffineCover.f i) W.hom (X.directedAffineCover.f j)
      (𝟙 W.left) (X.directedAffineCover.trans h) (𝟙 X) (by simp)
        ((Category.comp_id _).trans (X.directedAffineCover.trans_map h).symm) ≫
        pullback.snd W.hom (X.directedAffineCover.f j) =
      pullback.snd W.hom (X.directedAffineCover.f i) ≫ X.directedAffineCover.trans h
  simp

/-- The transition viewed as a morphism in the target affine slice. -/
def affineBaseCoverSliceTransition {i j : X.directedAffineCover.I₀} (h : i ⟶ j) :
    (Over.map ((FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).map h)).obj (affineBaseCoverSlice W i) ⟶
      affineBaseCoverSlice W j :=
  Over.homMk (affineBaseCoverTransition W h) (affineBaseCoverTransition_open W h)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseCover.Construction
