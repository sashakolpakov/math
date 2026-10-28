import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseCover

/-! # Base Cover Functoriality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseCoverFunctoriality.Construction

noncomputable section

/-!
# Completion: functoriality of the pulled-back affine cover

An actual site morphism induces maps on each pulled-back affine open. If
the original object already maps to an affine open, its cover projection
has the canonical section supplied by the pullback universal property.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} {V W : X.ProEt}

/-- The scheme map between members of the pulled-back affine base covers. -/
def affineBaseCoverChangeScheme (g : V ⟶ W) (i : X.directedAffineCover.I₀) :
    (BaseCover.Construction.affineBaseCover V).X i ⟶ (BaseCover.Construction.affineBaseCover W).X i :=
  pullback.lift (pullback.fst V.hom (X.directedAffineCover.f i) ≫ g.left)
    (pullback.snd V.hom (X.directedAffineCover.f i)) (by
      rw [Category.assoc, MorphismProperty.Over.w]
      exact pullback.condition)

/-- The induced map is an actual morphism in the original site. -/
def affineBaseCoverChange (g : V ⟶ W) (i : X.directedAffineCover.I₀) :
    BaseCover.Construction.affineBaseCoverObject V i ⟶ BaseCover.Construction.affineBaseCoverObject W i :=
  MorphismProperty.Over.homMk (affineBaseCoverChangeScheme g i) (by
    change affineBaseCoverChangeScheme g i ≫
      pullback.fst W.hom (X.directedAffineCover.f i) ≫ W.hom =
        pullback.fst V.hom (X.directedAffineCover.f i) ≫ V.hom
    simp [affineBaseCoverChangeScheme, Category.assoc])

theorem affineBaseCoverChange_projection (g : V ⟶ W) (i : X.directedAffineCover.I₀) :
    affineBaseCoverChange g i ≫ BaseCover.Construction.affineBaseCoverProjection W i = BaseCover.Construction.affineBaseCoverProjection V i ≫ g := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

theorem affineBaseCoverChange_open (g : V ⟶ W) (i : X.directedAffineCover.I₀) :
    affineBaseCoverChange g i ≫ BaseCover.Construction.affineBaseCoverToOpen W i = BaseCover.Construction.affineBaseCoverToOpen V i := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

/-- The same induced map in the affine slice. -/
def affineBaseCoverChangeSlice (g : V ⟶ W) (i : X.directedAffineCover.I₀) :
    BaseCover.Construction.affineBaseCoverSlice V i ⟶ BaseCover.Construction.affineBaseCoverSlice W i :=
  Over.homMk (affineBaseCoverChange g i) (affineBaseCoverChange_open g i)

/-- A map into a base affine open supplies a section of its pulled-back cover projection. -/
def affineBaseCoverSection (i : X.directedAffineCover.I₀)
    (a : V ⟶ (FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) : V ⟶ BaseCover.Construction.affineBaseCoverObject V i :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 V.left) a.left (by
      rw [Category.id_comp]
      exact (MorphismProperty.Over.w a).symm))
    (by
      change pullback.lift (𝟙 V.left) a.left _ ≫
        pullback.fst V.hom (X.directedAffineCover.f i) ≫ V.hom = V.hom
      simp)

theorem affineBaseCoverSection_projection (i : X.directedAffineCover.I₀)
    (a : V ⟶ (FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) :
    affineBaseCoverSection i a ≫ BaseCover.Construction.affineBaseCoverProjection V i = 𝟙 V := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

theorem affineBaseCoverSection_open (i : X.directedAffineCover.I₀)
    (a : V ⟶ (FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) :
    affineBaseCoverSection i a ≫ BaseCover.Construction.affineBaseCoverToOpen V i = a := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_snd _ _ _

/-- The section considered as a map in the affine slice. -/
def affineBaseCoverSectionSlice (i : X.directedAffineCover.I₀)
    (a : V ⟶ (FiniteTorsor.GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) : Over.mk a ⟶ BaseCover.Construction.affineBaseCoverSlice V i :=
  Over.homMk (affineBaseCoverSection i a) (affineBaseCoverSection_open i a)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseCoverFunctoriality.Construction
