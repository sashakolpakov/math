import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineTangentLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberEtaleMap

/-! # Affine Derivation Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineDerivationRestriction

noncomputable section

/-! The actual affine open restrictions of the family give linear
maps of derivations with fixed-fiber coefficients. They retain the
original ring maps and respect identities and successive restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k] (X : Over (Spec (.of R)))

attribute [local instance 50] AffineTangentLifts.familyAffineCoefficientAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [Algebra k R] [Algebra R k] [IsScalarTower k R k] in
theorem familyAffineCoordinateMap_id (V : X.left.affineOpens) :
    Affine.OpenDiagram.familyAffineCoordinateMap R X (le_refl V.1) = AlgHom.id R (AffineTangentLifts.familyAffineRing R X V) := by
  unfold Affine.OpenDiagram.familyAffineCoordinateMap
  rw [Affine.OpenDiagram.familyOpenMap_id]
  exact HilbertConstruction.Affine.OverFunctoriality.affineOverMap_id R ((Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)

omit [Algebra k R] [Algebra R k] [IsScalarTower k R k] in
theorem familyAffineCoordinateMap_comp {U V W : X.left.affineOpens} (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    Affine.OpenDiagram.familyAffineCoordinateMap R X (h.trans j) =
      (Affine.OpenDiagram.familyAffineCoordinateMap R X h).comp (Affine.OpenDiagram.familyAffineCoordinateMap R X j) := by
  unfold Affine.OpenDiagram.familyAffineCoordinateMap
  rw [← Affine.OpenDiagram.familyOpenMap_comp X h j]
  exact HilbertConstruction.Affine.OverFunctoriality.affineOverMap_comp R
    (X := (Affine.OpenDiagram.familyAffineOpenDiagram X).obj U) (Y := (Affine.OpenDiagram.familyAffineOpenDiagram X).obj V)
    (Z := (Affine.OpenDiagram.familyAffineOpenDiagram X).obj W) (Affine.OpenDiagram.familyOpenMap X h) (Affine.OpenDiagram.familyOpenMap X j)

def familyAffineDerivationRestriction {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    Derivation k (AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W) →ₗ[k]
      Derivation k (AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V) := by
  have := AffineTangentLifts.familyAffineCoefficientTower k R X V
  have := AffineTangentLifts.familyAffineCoefficientTower k R X W
  exact PointFiberEtaleMap.pointFiberEtaleDerivationMap k R (AffineTangentLifts.familyAffineRing R X W) (AffineTangentLifts.familyAffineRing R X V)
    (Affine.OpenDiagram.familyAffineCoordinateMap R X h) (Affine.OpenDiagram.familyAffineCoordinateMap_etale R X h)

theorem familyAffineDerivationRestriction_apply {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (d : Derivation k (AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] AffineTangentLifts.familyAffineRing R X W))
    (a : AffineTangentLifts.familyAffineRing R X W) :
    familyAffineDerivationRestriction k R X h d (Affine.OpenDiagram.familyAffineCoordinateMap R X h a) =
      Algebra.TensorProduct.map (AlgHom.id k k) (Affine.OpenDiagram.familyAffineCoordinateMap R X h) (d a) := by
  have := AffineTangentLifts.familyAffineCoefficientTower k R X V
  have := AffineTangentLifts.familyAffineCoefficientTower k R X W
  exact PointFiberEtaleMap.pointFiberEtaleDerivationMap_apply k R (AffineTangentLifts.familyAffineRing R X W) (AffineTangentLifts.familyAffineRing R X V)
    (Affine.OpenDiagram.familyAffineCoordinateMap R X h) (Affine.OpenDiagram.familyAffineCoordinateMap_etale R X h) d a

theorem familyAffineDerivationRestriction_id (V : X.left.affineOpens) :
    familyAffineDerivationRestriction k R X (le_refl V.1) = LinearMap.id := by
  have := AffineTangentLifts.familyAffineCoefficientTower k R X V
  have hq := familyAffineCoordinateMap_id R X V
  have he : (AlgHom.id R (AffineTangentLifts.familyAffineRing R X V)).toRingHom.Etale :=
    hq ▸ Affine.OpenDiagram.familyAffineCoordinateMap_etale R X (le_refl V.1)
  exact (PointFiberEtaleMap.pointFiberEtaleDerivationMap_congr k R _ _ _ _
    (Affine.OpenDiagram.familyAffineCoordinateMap_etale R X (le_refl V.1)) he hq).trans
    (PointFiberEtaleMap.pointFiberEtaleDerivationMap_id k R _ he)

theorem familyAffineDerivationRestriction_comp {U V W : X.left.affineOpens}
    (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    (familyAffineDerivationRestriction k R X h).comp (familyAffineDerivationRestriction k R X j) =
      familyAffineDerivationRestriction k R X (h.trans j) := by
  have := AffineTangentLifts.familyAffineCoefficientTower k R X U
  have := AffineTangentLifts.familyAffineCoefficientTower k R X V
  have := AffineTangentLifts.familyAffineCoefficientTower k R X W
  have hq := familyAffineCoordinateMap_comp R X h j
  have he : ((Affine.OpenDiagram.familyAffineCoordinateMap R X h).comp
      (Affine.OpenDiagram.familyAffineCoordinateMap R X j)).toRingHom.Etale :=
    hq ▸ Affine.OpenDiagram.familyAffineCoordinateMap_etale R X (h.trans j)
  exact (PointFiberEtaleMap.pointFiberEtaleDerivationMap_comp k R _ _ _ (Affine.OpenDiagram.familyAffineCoordinateMap R X j)
    (Affine.OpenDiagram.familyAffineCoordinateMap R X h) (Affine.OpenDiagram.familyAffineCoordinateMap_etale R X j)
    (Affine.OpenDiagram.familyAffineCoordinateMap_etale R X h) he).symm.trans
    (PointFiberEtaleMap.pointFiberEtaleDerivationMap_congr k R _ _ _ _
      (Affine.OpenDiagram.familyAffineCoordinateMap_etale R X (h.trans j)) he hq).symm

def familyAffineCoefficientDerivationPresheaf : X.left.affineOpensᵒᵖ ⥤ ModuleCat k where
  obj V := ModuleCat.of k
    (Derivation k (AffineTangentLifts.familyAffineRing R X V.unop) (k ⊗[R] AffineTangentLifts.familyAffineRing R X V.unop))
  map f := ModuleCat.ofHom (familyAffineDerivationRestriction k R X f.unop.le)
  map_id V := ModuleCat.hom_ext (familyAffineDerivationRestriction_id k R X V.unop)
  map_comp f g := ModuleCat.hom_ext
    (familyAffineDerivationRestriction_comp k R X g.unop.le f.unop.le).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineDerivationRestriction
