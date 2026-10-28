import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Open Diagram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenDiagram

noncomputable section

/-! The actual affine open subfamilies of a family over an affine base
form a diagram. Their coordinate maps are etale, and their coordinate
algebras are smooth whenever the original family is smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme} (X : Over S)

def familyOpenMap {V W : X.left.Opens} (h : V ≤ W) :
    HilbertConstruction.Open.ParameterPoints.openParameterScheme X V ⟶ HilbertConstruction.Open.ParameterPoints.openParameterScheme X W :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ (W.ι ≫ X.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])

theorem familyOpenMap_inclusion {V W : X.left.Opens} (h : V ≤ W) :
    familyOpenMap X h ≫ HilbertConstruction.Open.ParameterPoints.openParameterInclusion X W = HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι X.left h

instance familyOpenMap_open {V W : X.left.Opens} (h : V ≤ W) :
    IsOpenImmersion (familyOpenMap X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE h))

theorem familyOpenMap_id (V : X.left.Opens) :
    familyOpenMap X (le_refl V) = 𝟙 (HilbertConstruction.Open.ParameterPoints.openParameterScheme X V) := by
  have : Mono (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V) :=
    Over.mono_of_mono_left (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V)
  apply (cancel_mono (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X V)).mp
  rw [familyOpenMap_inclusion, Category.id_comp]

theorem familyOpenMap_comp {U V W : X.left.Opens} (h : U ≤ V) (j : V ≤ W) :
    familyOpenMap X h ≫ familyOpenMap X j = familyOpenMap X (h.trans j) := by
  have : Mono (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X W) :=
    Over.mono_of_mono_left (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X W)
  apply (cancel_mono (HilbertConstruction.Open.ParameterPoints.openParameterInclusion X W)).mp
  rw [Category.assoc, familyOpenMap_inclusion, familyOpenMap_inclusion, familyOpenMap_inclusion]

def familyAffineOpenDiagram : X.left.affineOpens ⥤ Over S where
  obj V := HilbertConstruction.Open.ParameterPoints.openParameterScheme X V.1
  map f := familyOpenMap X f.le
  map_id V := familyOpenMap_id X V.1
  map_comp f g := (familyOpenMap_comp X f.le g.le).symm

instance familyAffineOpenDiagram_affine (V : X.left.affineOpens) :
    IsAffine ((familyAffineOpenDiagram X).obj V).left := V.2

instance familyAffineOpenDiagram_smooth [Smooth X.hom] (V : X.left.affineOpens) :
    Smooth ((familyAffineOpenDiagram X).obj V).hom :=
  inferInstanceAs (Smooth (V.1.ι ≫ X.hom))

variable (R : Type) [CommRing R] (Y : Over (Spec (.of R)))

def familyAffineCoordinateFunctor : Y.left.affineOpensᵒᵖ ⥤ CommAlgCat R :=
  HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor R (familyAffineOpenDiagram Y)

theorem familyAffineCoordinate_smooth [Smooth Y.hom] (V : Y.left.affineOpens) :
    Algebra.Smooth R ((familyAffineCoordinateFunctor R Y).obj (Opposite.op V)) :=
  HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth R ((familyAffineOpenDiagram Y).obj V)

def familyAffineCoordinateMap {V W : Y.left.affineOpens} (h : V.1 ≤ W.1) :
    HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R ((familyAffineOpenDiagram Y).obj W) →ₐ[R]
      HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra R ((familyAffineOpenDiagram Y).obj V) :=
  HilbertConstruction.Affine.OverMorphisms.affineOverMap R (X := (familyAffineOpenDiagram Y).obj V)
    (Y := (familyAffineOpenDiagram Y).obj W) (familyOpenMap Y h)

theorem familyAffineCoordinateMap_etale {V W : Y.left.affineOpens} (h : V.1 ≤ W.1) :
    (familyAffineCoordinateMap R Y h).toRingHom.Etale := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (familyAffineCoordinateMap R Y h).toRingHom)) :=
    @HilbertConstruction.Affine.OverMorphisms.affineOverMap_isOpenImmersion R _ ((familyAffineOpenDiagram Y).obj V)
      ((familyAffineOpenDiagram Y).obj W) _ _ (familyOpenMap Y h) (familyOpenMap_open Y h)
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstanceAs (Etale (Spec.map (CommRingCat.ofHom
      (familyAffineCoordinateMap R Y h).toRingHom))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenDiagram
