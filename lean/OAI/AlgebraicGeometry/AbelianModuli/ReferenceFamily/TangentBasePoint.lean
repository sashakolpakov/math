import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDualScalarTowers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

/-! # Tangent Base Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint

noncomputable section

section

/-! A base tangent gives an actual dual-number test morphism. The
special fiber of its pullback is naturally the fixed original fiber,
with the literal equality of the composed base maps retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k]

def tangentBasePoint (d : Derivation k R k) : Spec (.of (DualNumber k)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val.toRingHom))

theorem tangentBasePoint_reduction (d : Derivation k R k) :
    Smooth.AffineDualProduct.dualBaseReduction k ≫ tangentBasePoint k R d =
      Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val.toRingHom)) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (TangentDualScalarTowers.baseTangentDualAlgebra_reduction k R d)

def tangentFamily (X : Over (Spec (.of R))) (d : Derivation k R k) : Over (Spec (.of (DualNumber k))) :=
  (Over.pullback (tangentBasePoint k R d)).obj X

def fixedFamilyFiber (X : Over (Spec (.of R))) : Over (Spec (.of k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))).obj X

def tangentFamilyFiberIso (d : Derivation k R k) :
    Over.pullback (tangentBasePoint k R d) ⋙ Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k))) :=
  (Over.pullbackComp (Smooth.AffineDualProduct.dualBaseReduction k) (tangentBasePoint k R d)).symm ≪≫
    eqToIso (congrArg (fun f : Spec (.of k) ⟶ Spec (.of R) => Over.pullback f)
      (tangentBasePoint_reduction k R d))

end

section

/-! The actual dual-number point retains and detects the original
base derivation. It is a morphism over the original coefficient field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k]

theorem tangentBaseLift_snd (d : Derivation k R k) (r : R) :
    (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r).snd = d r := by
  have h := Derivation.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).apply_symm_apply d) r
  rw [Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply] at h
  exact h

theorem tangentBasePoint_injective : Function.Injective (tangentBasePoint k R) := by
  intro d e h
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  apply Derivation.ext
  intro r
  have hs := congrArg (fun f : R →+* DualNumber k => (f r).snd) hr
  exact (tangentBaseLift_snd k R d r).symm.trans (hs.trans (tangentBaseLift_snd k R e r))

theorem tangentBasePoint_overField (d : Derivation k R k) :
    tangentBasePoint k R d ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Smooth.AffineDualProduct.dualBaseProjection k := by
  change Spec.map (CommRingCat.ofHom (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val.commutes)

end

/-! The zero derivation gives exactly the constant extension of
the original base point. The same constant map is recovered by reducing
any of the actual tangent points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k R : Type) [Field k] [CommRing R] [Algebra k R] [Algebra R k]
    [IsScalarTower k R k]

theorem tangentBasePoint_zero : tangentBasePoint k R 0 =
    Smooth.AffineDualProduct.dualBaseProjection k ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
  change Spec.map (CommRingCat.ofHom (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm 0).val.toRingHom)) =
    Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · exact TangentDualScalarTowers.baseTangentDualAlgebra_reduction k R 0 r
  · change (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm 0).val r).snd = 0
    rw [tangentBaseLift_snd]
    rfl

theorem tangentBasePoint_zero_constant (d : Derivation k R k) :
    tangentBasePoint k R 0 = Smooth.AffineDualProduct.dualBaseProjection k ≫ Smooth.AffineDualProduct.dualBaseReduction k ≫ tangentBasePoint k R d := by
  rw [tangentBasePoint_reduction, tangentBasePoint_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint
