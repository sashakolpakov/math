import OAI.RepresentationTheory.Theta.Geometric.Affine.StructureCoordinates
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base Change Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.BaseChangeCoordinates

noncomputable section

section

/-! The native affine base-change chart has its actual projection
identified with the tensor inclusion, over an arbitrary parameter ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {X : Scheme} [IsAffine X] (h : X ⟶ Spec (.of A))

def affineBaseChangeCoordinateIso :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    pullback h (Spec.map (CommRingCat.ofHom (algebraMap A R))) ≅
      Spec (.of (Γ(X, ⊤) ⊗[A] R)) := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  let a := pullback.map h (Spec.map (CommRingCat.ofHom (algebraMap A R)))
    (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
    (Spec.map (CommRingCat.ofHom (algebraMap A R))) X.isoSpec.hom (𝟙 _) (𝟙 _)
    (by simp only [Category.comp_id, StructureCoordinates.affineStructure_specMap, Iso.hom_inv_id_assoc])
    (by simp only [Category.comp_id, Category.id_comp])
  have : IsIso a := by dsimp only [a]; infer_instance
  exact asIso a ≪≫ pullbackSpecIso A Γ(X, ⊤) R

set_option backward.isDefEq.respectTransparency false in
theorem affineBaseChangeCoordinateIso_hom_fst :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineBaseChangeCoordinateIso (R := R) h).hom ≫
        FlatAffineFunctionDescent.flatEqualizerSpecMap A R Γ(X, ⊤) =
      pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A R))) ≫ X.isoSpec.hom := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  have hp : (pullbackSpecIso A Γ(X, ⊤) R).hom ≫ FlatAffineFunctionDescent.flatEqualizerSpecMap A R Γ(X, ⊤) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap A R))) :=
    pullbackSpecIso_hom_fst A Γ(X, ⊤) R
  simp only [affineBaseChangeCoordinateIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [hp]
  simp

theorem affineBaseChangeCoordinateIso_inv_fst :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineBaseChangeCoordinateIso (R := R) h).inv ≫
        pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap A R))) =
      FlatAffineFunctionDescent.flatEqualizerSpecMap A R Γ(X, ⊤) ≫ X.isoSpec.inv := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  apply (cancel_mono X.isoSpec.hom).mp
  rw [Category.assoc, ← affineBaseChangeCoordinateIso_hom_fst h,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

/-! Both projections and parameter changes of the actual affine
base-change chart agree with the corresponding tensor algebra maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {X : Scheme} [IsAffine X] (h : X ⟶ Spec (.of A))

theorem affineBaseChangeCoordinateIso_hom_snd :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineBaseChangeCoordinateIso (R := R) h).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[A] Γ(X, ⊤) ⊗[A] R).toRingHom) =
      pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  simp only [affineBaseChangeCoordinateIso, Iso.trans_hom, asIso_hom, Category.assoc]
  simp

def affineIsPullbackCoordinateIso {Z : Scheme} (u : Z ⟶ X) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    Z ≅ Spec (.of (Γ(X, ⊤) ⊗[A] R)) :=
  H.isoPullback ≪≫ affineBaseChangeCoordinateIso h

theorem affineIsPullbackCoordinateIso_hom_fst {Z : Scheme} (u : Z ⟶ X) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineIsPullbackCoordinateIso h u v H).hom ≫ FlatAffineFunctionDescent.flatEqualizerSpecMap A R Γ(X, ⊤) =
      u ≫ X.isoSpec.hom := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  dsimp only [affineIsPullbackCoordinateIso, Iso.trans_hom]
  rw [Category.assoc, affineBaseChangeCoordinateIso_hom_fst,
    ← Category.assoc, H.isoPullback_hom_fst]

theorem affineIsPullbackCoordinateIso_hom_snd {Z : Scheme} (u : Z ⟶ X) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineIsPullbackCoordinateIso h u v H).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[A] Γ(X, ⊤) ⊗[A] R).toRingHom) = v := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  simp only [affineIsPullbackCoordinateIso, Iso.trans_hom, Category.assoc,
    affineBaseChangeCoordinateIso_hom_snd, H.isoPullback_hom_snd]

theorem affineIsPullbackCoordinateIso_inv_fst {Z : Scheme} (u : Z ⟶ X) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineIsPullbackCoordinateIso h u v H).inv ≫ u =
      FlatAffineFunctionDescent.flatEqualizerSpecMap A R Γ(X, ⊤) ≫ X.isoSpec.inv := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  apply (cancel_mono X.isoSpec.hom).mp
  rw [Category.assoc, ← affineIsPullbackCoordinateIso_hom_fst h u v H,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem affineIsPullbackCoordinateIso_inv_snd {Z : Scheme} (u : Z ⟶ X) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineIsPullbackCoordinateIso h u v H).inv ≫ v =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[A] Γ(X, ⊤) ⊗[A] R).toRingHom) := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  exact (congrArg (fun t => (affineIsPullbackCoordinateIso h u v H).inv ≫ t)
    (affineIsPullbackCoordinateIso_hom_snd h u v H).symm).trans
      ((affineIsPullbackCoordinateIso h u v H).inv_hom_id_assoc _)

theorem tensorSpecMap_fst {S B : Type} [CommRing S] [CommRing B] [Algebra A S] [Algebra A B]
    (f : S →ₐ[A] R) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B) f).toRingHom) ≫
      FlatAffineFunctionDescent.flatEqualizerSpecMap A S B = FlatAffineFunctionDescent.flatEqualizerSpecMap A R B := by
  unfold FlatAffineFunctionDescent.flatEqualizerSpecMap
  rw [← Spec.map_comp]
  congr 1
  ext b
  change Algebra.TensorProduct.map (AlgHom.id A B) f (b ⊗ₜ[A] 1) = b ⊗ₜ[A] 1
  simp

theorem tensorSpecMap_snd {S B : Type} [CommRing S] [CommRing B] [Algebra A S] [Algebra A B]
    (f : S →ₐ[A] R) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B) f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S →ₐ[A] B ⊗[A] S).toRingHom) =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem affineIsPullbackCoordinateIso_natural
    {S : Type} [CommRing S] [Algebra A S] (f : S →ₐ[A] R)
    {ZR ZS : Scheme} (uR : ZR ⟶ X) (vR : ZR ⟶ Spec (.of R))
    (HR : IsPullback uR vR h (Spec.map (CommRingCat.ofHom (algebraMap A R))))
    (uS : ZS ⟶ X) (vS : ZS ⟶ Spec (.of S))
    (HS : IsPullback uS vS h (Spec.map (CommRingCat.ofHom (algebraMap A S))))
    (b : ZR ⟶ ZS) (hbX : b ≫ uS = uR)
    (hbS : b ≫ vS = vR ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) :
    let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
    (affineIsPullbackCoordinateIso h uR vR HR).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A Γ(X, ⊤)) f).toRingHom) =
      b ≫ (affineIsPullbackCoordinateIso h uS vS HS).hom := by
  let : Algebra A Γ(X, ⊤) := StructureCoordinates.affineStructureAlgebra h
  apply (cancel_mono (affineIsPullbackCoordinateIso h uS vS HS).inv).mp
  rw [Category.assoc b, Iso.hom_inv_id, Category.comp_id]
  apply HS.hom_ext
  · simp only [Category.assoc, affineIsPullbackCoordinateIso_inv_fst]
    rw [← Category.assoc _ (FlatAffineFunctionDescent.flatEqualizerSpecMap A S Γ(X, ⊤)), tensorSpecMap_fst]
    rw [← Category.assoc, affineIsPullbackCoordinateIso_hom_fst, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, hbX]
  · simp only [Category.assoc, affineIsPullbackCoordinateIso_inv_snd]
    rw [tensorSpecMap_snd, ← Category.assoc, affineIsPullbackCoordinateIso_hom_snd, hbS]

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.BaseChangeCoordinates
