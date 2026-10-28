import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenDiagram
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.BaseChangeCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackCartesianMap

/-! # Affine Diagram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram

noncomputable section

section

/-! The affine-open diagram of the actual fixed fiber is naturally
identified with its literal tensor algebras. These comparisons retain
every original open restriction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R)))

def fixedFiberAffineDiagram : X.left.affineOpens ⥤ Over (Spec (.of k)) :=
  Affine.OpenDiagram.familyAffineOpenDiagram X ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))

def fixedFiberTensorAlgebras : X.left.affineOpensᵒᵖ ⥤ CommAlgCat k :=
  Affine.OpenDiagram.familyAffineCoordinateFunctor R X ⋙ HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor R k

def fixedFiberTensorDiagram : X.left.affineOpens ⥤ Over (Spec (.of k)) :=
  HilbertConstruction.AlgebraSchemeDiagrams.algebraSchemeDiagram k (fixedFiberTensorAlgebras R k X)

def fixedFiberAffineCoordinates : fixedFiberAffineDiagram R k X ≅ fixedFiberTensorDiagram R k X :=
  NatIso.ofComponents
    (fun V => Affine.BaseChangeCoordinates.affineBaseChangeCoordinates R k ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V))
    (fun h => (Affine.BaseChangeCoordinates.affineBaseChangeCoordinates_natural R k ((Affine.OpenDiagram.familyAffineOpenDiagram X).map h)).symm)

instance fixedFiberAffineDiagram_affine (V : X.left.affineOpens) :
    IsAffine ((fixedFiberAffineDiagram R k X).obj V).left := by
  change IsAffine (CategoryTheory.Limits.pullback ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V).hom
    (Spec.map (CommRingCat.ofHom (algebraMap R k))))
  infer_instance

theorem fixedFiberAffineMap_open {V W : X.left.affineOpens} (h : V ⟶ W) :
    IsOpenImmersion (((fixedFiberAffineDiagram R k X).map h).left) :=
  @OverPullbackCartesianMap.overPullback_map_open _ _ (Spec.map (CommRingCat.ofHom (algebraMap R k)))
    ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V) ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj W)
    ((Affine.OpenDiagram.familyAffineOpenDiagram X).map h) (Affine.OpenDiagram.familyOpenMap_open X h.le)

theorem fixedFiberTensorMap_open {V W : X.left.affineOpens} (h : V ⟶ W) :
    IsOpenImmersion (((fixedFiberTensorDiagram R k X).map h).left) := by
  let e := fixedFiberAffineCoordinates R k X
  have he : (fixedFiberTensorDiagram R k X).map h =
      (e.app V).inv ≫ (fixedFiberAffineDiagram R k X).map h ≫ (e.app W).hom := by
    change _ = (e.app V).inv ≫
      ((fixedFiberAffineDiagram R k X).map h ≫ e.hom.app W)
    rw [e.hom.naturality h, ← Category.assoc]
    exact ((e.app V).inv_hom_id_assoc _).symm
  have : IsOpenImmersion (((fixedFiberAffineDiagram R k X).map h).left) :=
    fixedFiberAffineMap_open R k X h
  have : IsIso (e.app V).inv.left := (Over.forget _).map_isIso (e.app V).inv
  have : IsIso (e.app W).hom.left := (Over.forget _).map_isIso (e.app W).hom
  rw [he]
  change IsOpenImmersion ((e.app V).inv.left ≫
    ((fixedFiberAffineDiagram R k X).map h).left ≫ (e.app W).hom.left)
  infer_instance

theorem fixedFiberTensorAlgebraMap_etale {V W : X.left.affineOpensᵒᵖ} (h : V ⟶ W) :
    (((fixedFiberTensorAlgebras R k X).map h).hom.toRingHom).Etale := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (((fixedFiberTensorAlgebras R k X).map h).hom.toRingHom))) :=
    fixedFiberTensorMap_open R k X h.unop
  have he : Etale (Spec.map (CommRingCat.ofHom
      (((fixedFiberTensorAlgebras R k X).map h).hom.toRingHom))) := inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (((fixedFiberTensorAlgebras R k X).map h).hom.toRingHom))).mp he

end

/-! Both the actual affine fibers and their tensor-coordinate
schemes embed as the original open subfamilies of the fixed fiber.
These inclusions commute with all affine restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R)))

def fixedFiberAffineInclusion (V : X.left.affineOpens) :
    (fixedFiberAffineDiagram R k X).obj V ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V.1)

instance fixedFiberAffineInclusion_open (V : X.left.affineOpens) :
    IsOpenImmersion (fixedFiberAffineInclusion R k X V).left :=
  OverPullbackCartesianMap.overPullback_map_open (Spec.map (CommRingCat.ofHom (algebraMap R k))) (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V.1)

theorem fixedFiberAffineInclusion_natural {V W : X.left.affineOpens} (f : V ⟶ W) :
    (fixedFiberAffineDiagram R k X).map f ≫ fixedFiberAffineInclusion R k X W =
      fixedFiberAffineInclusion R k X V := by
  change (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map (Affine.OpenDiagram.familyOpenMap X f.le) ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).map (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X W.1) = _
  rw [← Functor.map_comp, Affine.OpenDiagram.familyOpenMap_inclusion]
  rfl

def fixedFiberTensorInclusion (V : X.left.affineOpens) :
    (fixedFiberTensorDiagram R k X).obj V ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X :=
  (fixedFiberAffineCoordinates R k X).inv.app V ≫ fixedFiberAffineInclusion R k X V

instance fixedFiberTensorInclusion_open (V : X.left.affineOpens) :
    IsOpenImmersion (fixedFiberTensorInclusion R k X V).left := by
  have : IsIso ((fixedFiberAffineCoordinates R k X).inv.app V).left :=
    (Over.forget _).map_isIso ((fixedFiberAffineCoordinates R k X).inv.app V)
  change IsOpenImmersion (((fixedFiberAffineCoordinates R k X).inv.app V).left ≫
    (fixedFiberAffineInclusion R k X V).left)
  infer_instance

theorem fixedFiberTensorInclusion_natural {V W : X.left.affineOpens} (f : V ⟶ W) :
    (fixedFiberTensorDiagram R k X).map f ≫ fixedFiberTensorInclusion R k X W =
      fixedFiberTensorInclusion R k X V := by
  unfold fixedFiberTensorInclusion
  rw [← Category.assoc, (fixedFiberAffineCoordinates R k X).inv.naturality f,
    Category.assoc, fixedFiberAffineInclusion_natural]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram
