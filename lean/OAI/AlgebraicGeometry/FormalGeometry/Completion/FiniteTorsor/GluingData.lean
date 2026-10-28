import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.AffineSlices
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceRepresentativePullback
import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Gluing Data -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GluingData.Construction

noncomputable section

/-!
# Completion: actual relative gluing data for a finite torsor

The finite étale representatives on affine opens and their proved pullback
transition maps form relative gluing data over the directed affine cover.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (X : Scheme.{u})

/-- The directed affine open cover, considered as objects of the actual pro-étale site. -/
def proEtaleDirectedAffineDiagram : X.directedAffineCover.I₀ ⥤ X.ProEt where
  obj i := Scheme.ProEt.mk (X.directedAffineCover.f i)
  map h := MorphismProperty.Over.homMk (X.directedAffineCover.trans h)
    (X.directedAffineCover.trans_map h)
  map_id i := MorphismProperty.Over.Hom.ext (X.directedAffineCover.trans_id i)
  map_comp h k := MorphismProperty.Over.Hom.ext (X.directedAffineCover.trans_comp h k)

instance (i : X.directedAffineCover.I₀) : IsAffine ((proEtaleDirectedAffineDiagram X).obj i).left :=
  i.2

namespace FiniteCoefficientExtension

variable {X} {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- The actual representative chosen over an affine object. -/
def _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension.affineSliceObject (U : X.ProEt) [IsAffine U.left] : Over U :=
  (E.exists_finiteEtale_representative_affine_slice U).choose

theorem _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension.affineSliceObject_finite (U : X.ProEt) [IsAffine U.left] :
    IsFinite (E.affineSliceObject U).hom.left :=
  (E.exists_finiteEtale_representative_affine_slice U).choose_spec.1

theorem _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension.affineSliceObject_etale (U : X.ProEt) [IsAffine U.left] :
    Etale (E.affineSliceObject U).hom.left :=
  (E.exists_finiteEtale_representative_affine_slice U).choose_spec.2.1

/-- The chosen object's actual representing bijection on the affine slice. -/
def _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension.affineSliceRepresentative (U : X.ProEt) [IsAffine U.left] :
    ((Over.forget U).op ⋙ E.fiberPresheaf).RepresentableBy (E.affineSliceObject U) :=
  (E.exists_finiteEtale_representative_affine_slice U).choose_spec.2.2.some

/-- Relative gluing data built from the actual affine representatives and their canonical transitions. -/
def _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension.relativeGluingData : X.directedAffineCover.RelativeGluingData where
  functor := SliceRepresentativePullback.Construction.sliceRepresentativeDiagram E.fiberPresheaf (proEtaleDirectedAffineDiagram X)
    (fun i => E.affineSliceObject ((proEtaleDirectedAffineDiagram X).obj i))
    (fun i => E.affineSliceRepresentative ((proEtaleDirectedAffineDiagram X).obj i)) ⋙
      Scheme.ProEt.forget X ⋙ Over.forget X
  natTrans := Functor.whiskerRight
    (SliceRepresentativePullback.Construction.sliceRepresentativeDiagramToBase E.fiberPresheaf (proEtaleDirectedAffineDiagram X)
      (fun i => E.affineSliceObject ((proEtaleDirectedAffineDiagram X).obj i))
      (fun i => E.affineSliceRepresentative ((proEtaleDirectedAffineDiagram X).obj i)))
    (Scheme.ProEt.forget X ⋙ Over.forget X)
  equifibered := by
    intro i j h
    exact (SliceRepresentativePullback.Construction.sliceRepresentativeMap_isPullback E.fiberPresheaf
      (E.affineSliceRepresentative ((proEtaleDirectedAffineDiagram X).obj i))
      (E.affineSliceRepresentative ((proEtaleDirectedAffineDiagram X).obj j))
      ((proEtaleDirectedAffineDiagram X).map h)).map (Scheme.ProEt.forget X ⋙ Over.forget X)

/-- The actual scheme obtained by gluing the affine representatives. -/
def _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension.gluedScheme : Scheme.{u} := E.relativeGluingData.glued

/-- Its actual structure morphism to the original base. -/
def _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.FiniteCoefficientExtension.gluedSchemeToBase : E.gluedScheme ⟶ X := E.relativeGluingData.toBase

end FiniteCoefficientExtension

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GluingData.Construction
