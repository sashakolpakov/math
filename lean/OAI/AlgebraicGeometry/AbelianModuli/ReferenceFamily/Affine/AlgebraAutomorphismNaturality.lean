import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Algebra Automorphism Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality

noncomputable section

section

/-! The literal affine tensor presentation of a scheme pullback is
natural in algebra maps, as verified by its two pullback projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (R A B T : Type) [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]

def affineOverAlgHom (f : A →ₐ[R] B) : EtaleSplittingAt.EtaleSplitting.affineOver R B ⟶ EtaleSplittingAt.EtaleSplitting.affineOver R A :=
  (algSpec (CommRingCat.of R)).map
    (CommAlgCat.ofHom (X := A) (Y := B) f).op

theorem affineOverAlgHom_left (f : A →ₐ[R] B) :
    (affineOverAlgHom R A B f).left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

theorem affineBaseChangeIso_hom_fst :
    (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).hom.left ≫
      pullback.fst (EtaleSplittingAt.EtaleSplitting.affineOver R A).hom (Spec.map (CommRingCat.ofHom (algebraMap R T))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom) := by
  change ((pullbackSpecIso R T A).inv ≫ (pullbackSymmetry _ _).hom) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pullbackSpecIso_inv_snd R T A

theorem affineBaseChangeIso_natural (f : A →ₐ[R] B) :
    (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T).hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).map (affineOverAlgHom R A B f) =
      affineOverAlgHom T (T ⊗[R] A) (T ⊗[R] B)
          (Algebra.TensorProduct.map (AlgHom.id T T) f) ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T).hom.left ≫
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).map
          (affineOverAlgHom R A B f)).left) ≫ pullback.fst _ _ =
      ((affineOverAlgHom T (T ⊗[R] A) (T ⊗[R] B)
        (Algebra.TensorProduct.map (AlgHom.id T T) f)).left ≫
          (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).hom.left) ≫ pullback.fst _ _
    simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, affineBaseChangeIso_hom_fst, affineOverAlgHom_left,
      affineBaseChangeIso_hom_fst, affineOverAlgHom_left, ← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (1 : T) ⊗ₜ[R] f a =
      Algebra.TensorProduct.map (AlgHom.id T T) f ((1 : T) ⊗ₜ[R] a)
    rfl
  · exact (Over.w ((EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R B T).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).map
        (affineOverAlgHom R A B f))).trans
      (Over.w (affineOverAlgHom T (T ⊗[R] A) (T ⊗[R] B)
        (Algebra.TensorProduct.map (AlgHom.id T T) f) ≫ (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso R A T).hom)).symm

end

/-! An actual commuting algebra square gives the corresponding
commuting square of affine scheme automorphisms over the same base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem affineAlgIso_natural (q : A →ₐ[R] B) (e : A ≃ₐ[R] A) (f : B ≃ₐ[R] B)
    (h : q.comp e.toAlgHom = f.toAlgHom.comp q) :
    (EtaleSplittingAt.EtaleSplitting.affineAlgIso R B f).hom ≫ affineOverAlgHom R A B q =
      affineOverAlgHom R A B q ≫ (EtaleSplittingAt.EtaleSplitting.affineAlgIso R A e).hom := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom q.toRingHom) =
    Spec.map (CommRingCat.ofHom q.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality
