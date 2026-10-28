import OAI.RepresentationTheory.Theta.Geometric.Dual.Numbers
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

/-! # Tangents -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.Tangents

noncomputable section

/-! Derivations give precisely the actual affine dual-number scheme
points with prescribed reduction, via fully faithful relative Spec. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

universe u

theorem affineSpec_comp {k R S T : Type u} [CommRing k] [CommRing R] [CommRing S]
    [CommRing T] [Algebra k R] [Algebra k S] [Algebra k T]
    (f : R →ₐ[k] S) (g : S →ₐ[k] T) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k S T g ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R S f =
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R T (g.comp f) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)).symm

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  [Algebra R k] [IsScalarTower k R k]

def affineTangentOrigin : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k k ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k (DualNumber k) :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k (DualNumber k) k (TrivSqZeroExt.fstHom k k k)

def affineTangentBasePoint : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k k ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k R :=
  AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R k (IsScalarTower.toAlgHom k R k)

def affineTangentPoints :=
  {f : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k (DualNumber k) ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k R //
    affineTangentOrigin k ≫ f = affineTangentBasePoint k R}

theorem affineTangentPoint_condition (f : R →ₐ[k] DualNumber k) :
    affineTangentOrigin k ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R (DualNumber k) f =
      affineTangentBasePoint k R ↔ ∀ a, (f a).fst = algebraMap R k a := by
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k (DualNumber k) k (TrivSqZeroExt.fstHom k k k) ≫ _ = _ ↔ _
  rw [affineSpec_comp]
  change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R k ((TrivSqZeroExt.fstHom k k k).comp f) =
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R k (IsScalarTower.toAlgHom k R k) ↔ _
  rw [(AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R k).injective.eq_iff]
  exact ⟨fun h a => congrArg (fun h : R →ₐ[k] k => h a) h,
    fun h => AlgHom.ext h⟩

def affineTangentPointsEquiv :
    {f : R →ₐ[k] DualNumber k // ∀ a, (f a).fst = algebraMap R k a} ≃ affineTangentPoints k R where
  toFun f := ⟨AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R (DualNumber k) f.val,
    (affineTangentPoint_condition k R f.val).mpr f.property⟩
  invFun f := ⟨(AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R (DualNumber k)).symm f.val,
    (affineTangentPoint_condition k R _).mp
      (by rw [Equiv.apply_symm_apply]; exact f.property)⟩
  left_inv f := Subtype.ext ((AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R (DualNumber k)).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k R (DualNumber k)).apply_symm_apply f.val)

def derivationAffineTangentEquiv : Derivation k R k ≃ affineTangentPoints k R :=
  Dual.Numbers.derivationDualNumberEquiv.trans (affineTangentPointsEquiv k R)

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.Tangents
