import Mathlib.AlgebraicGeometry.Limits

/-! # Point Algebra Hom -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.PointAlgebraHom.Construction

noncomputable section

/-! Field-valued points of an actual affine scheme are algebra maps.
This standalone comparison has no dependence on statement modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def affinePointsEquivAlgHom
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R C))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≃ (B →ₐ[R] C) where
  toFun f :=
    { toRingHom := (Spec.preimage f.left).hom
      commutes' := fun r => by
        have hw : f.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
            Spec.map (CommRingCat.ofHom (algebraMap R C)) := f.w
        have h := congrArg Spec.preimage hw
        simp only [Spec.preimage_comp, Spec.preimage_map] at h
        exact congrArg (fun f => f.hom r) h }
  invFun f := Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)
  left_inv f := by
    apply Over.OverMorphism.ext
    exact Spec.map_preimage f.left
  right_inv f := by
    apply AlgHom.ext
    intro x
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))) x = f x
    rw [Spec.preimage_map]
    rfl

def affineFieldPointsEquivAlgHom
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    (Over.mk (𝟙 (Spec (.of R))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≃ (B →ₐ[R] R) := by
  simpa only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id] using
    affinePointsEquivAlgHom R B R

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.PointAlgebraHom.Construction
