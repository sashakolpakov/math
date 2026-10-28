import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.AffineDiagram
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleAlgebraDerivationFunctor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.AffineTangentLifts

/-! # Derivation Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.DerivationPresheaf

noncomputable section

section

/-! The literal fixed-fiber tensor algebras carry the derivation
presheaf whose restriction maps come from the actual open immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R)))

def fixedFiberDerivationPresheaf : X.left.affineOpensᵒᵖ ⥤ ModuleCat k :=
  EtaleAlgebraDerivationFunctor.etaleAlgebraDerivationFunctor k (AffineDiagram.fixedFiberTensorAlgebras R k X)
    (fun h => AffineDiagram.fixedFiberTensorAlgebraMap_etale R k X h)

def fixedFiberTensorRestriction {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) →ₐ[k] (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) :=
  Algebra.TensorProduct.map (AlgHom.id k k) (Affine.OpenDiagram.familyAffineCoordinateMap R X h)

theorem fixedFiberTensorRestriction_etale {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    (fixedFiberTensorRestriction R k X h).toRingHom.Etale :=
  AffineDiagram.fixedFiberTensorAlgebraMap_etale R k X (homOfLE h).op

def fixedFiberDerivationRestriction {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    Derivation k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) →ₗ[k]
      Derivation k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) :=
  EtaleHomDerivation.etaleAlgHomDerivationLinear (fixedFiberTensorRestriction R k X h)
    (fixedFiberTensorRestriction_etale R k X h)

theorem fixedFiberDerivationRestriction_presheaf {V W : X.left.affineOpens} (h : V.1 ≤ W.1) :
    fixedFiberDerivationRestriction R k X h =
      ((fixedFiberDerivationPresheaf R k X).map (homOfLE h).op).hom := rfl

end

/-! Literal fixed-fiber derivation restrictions preserve composition
and retain their value on functions from the larger affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R)))

theorem fixedFiberDerivationRestriction_apply {V W : X.left.affineOpens}
    (h : V.1 ≤ W.1)
    (d : Derivation k (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) (k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W))
    (a : k ⊗[R] Family.AffineTangentLifts.familyAffineRing R X W) :
    fixedFiberDerivationRestriction R k X h d (fixedFiberTensorRestriction R k X h a) =
      fixedFiberTensorRestriction R k X h (d a) :=
  EtaleHomDerivation.etaleAlgHomDerivationLinear_map (fixedFiberTensorRestriction R k X h)
    (fixedFiberTensorRestriction_etale R k X h) d a

theorem fixedFiberDerivationRestriction_comp {U V W : X.left.affineOpens}
    (t : U.1 ≤ V.1) (h : V.1 ≤ W.1) :
    (fixedFiberDerivationRestriction R k X t).comp (fixedFiberDerivationRestriction R k X h) =
      fixedFiberDerivationRestriction R k X (t.trans h) := by
  simp only [fixedFiberDerivationRestriction_presheaf]
  exact (congrArg (fun f => f.hom)
    ((fixedFiberDerivationPresheaf R k X).map_comp (homOfLE h).op (homOfLE t).op)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.DerivationPresheaf
