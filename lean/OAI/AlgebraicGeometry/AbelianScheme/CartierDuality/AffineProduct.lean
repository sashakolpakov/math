import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffinePullback

/-! # Affine Product -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineProduct

noncomputable section

/-!
# CartierDuality: natural affine product coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped TensorProduct
open MonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction

namespace Schemes

/-- The comparison from the slice product preserves the test-scheme
projection as well as the original group-scheme projection. -/
theorem sliceProductPullbackIso_snd (S : Scheme.{u}) (T Y : Over S) :
    ((SliceCharacters.Construction.Schemes.sliceProductPullbackIso S T).hom.app Y).left ≫ Limits.pullback.snd Y.hom T.hom =
      (Limits.prod.fst : T ⨯ Y ⟶ T).left := by
  have h := ((SliceCharacters.Construction.Schemes.sliceProductPullbackIso S T).hom.app Y).w
  change ((SliceCharacters.Construction.Schemes.sliceProductPullbackIso S T).hom.app Y).left ≫
      Limits.pullback.snd Y.hom T.hom = ((Over.star T).obj Y).hom.left at h
  apply h.trans
  exact congrArg (fun f : T ⨯ Y ⟶ T => f.left) (Limits.prod.lift_fst _ _)

/-- Comparison from the categorical product to the chosen Cartesian
monoidal product. -/
def productToTensor (S : Scheme.{u}) (T Y : Over S) : T ⨯ Y ⟶ T ⊗ Y :=
  CartesianMonoidalCategory.lift Limits.prod.fst Limits.prod.snd

/-- The comparison of the two product choices preserves the first projection. -/
theorem productToTensor_fst (S : Scheme.{u}) (T Y : Over S) :
    (productToTensor S T Y).left ≫ Limits.pullback.fst T.hom Y.hom =
      (Limits.prod.fst : T ⨯ Y ⟶ T).left :=
  congrArg (fun f : T ⨯ Y ⟶ T => f.left)
    (CartesianMonoidalCategory.lift_fst Limits.prod.fst Limits.prod.snd)

/-- The comparison of the two product choices preserves the second projection. -/
theorem productToTensor_snd (S : Scheme.{u}) (T Y : Over S) :
    (productToTensor S T Y).left ≫ Limits.pullback.snd T.hom Y.hom =
      (Limits.prod.snd : T ⨯ Y ⟶ Y).left :=
  congrArg (fun f : T ⨯ Y ⟶ Y => f.left)
    (CartesianMonoidalCategory.lift_snd Limits.prod.fst Limits.prod.snd)

/-- Changing either product factor commutes with the canonical comparison
between the two choices of categorical product. -/
theorem productToTensor_natural (S : Scheme.{u}) {T T' Y Y' : Over S}
    (f : T ⟶ T') (g : Y ⟶ Y') :
    Limits.prod.map f g ≫ productToTensor S T' Y' =
      productToTensor S T Y ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [productToTensor]
  · simp [productToTensor]

/-- The slice-product comparison is the product-choice comparison
followed by symmetry of the scheme-theoretic fiber product. -/
theorem sliceProductPullbackIso_eq_symmetry (S : Scheme.{u}) (T Y : Over S) :
    ((SliceCharacters.Construction.Schemes.sliceProductPullbackIso S T).hom.app Y).left =
      (productToTensor S T Y).left ≫ (Limits.pullbackSymmetry T.hom Y.hom).hom := by
  apply Limits.pullback.hom_ext
  · exact (SliceCharacters.Construction.Schemes.sliceProductPullbackIso_fst S T Y).trans
      ((congrArg (fun f => (productToTensor S T Y).left ≫ f)
        (Limits.pullbackSymmetry_hom_comp_fst T.hom Y.hom)).trans
          (productToTensor_snd S T Y)).symm
  · exact (sliceProductPullbackIso_snd S T Y).trans
      ((congrArg (fun f => (productToTensor S T Y).left ≫ f)
        (Limits.pullbackSymmetry_hom_comp_snd T.hom Y.hom)).trans
          (productToTensor_fst S T Y)).symm

end Schemes

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [HopfAlgebra R A]

/-- Tensor-product coordinates on the categorical product used to
evaluate a character section. -/
def affineProductCoordinates :
    (((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R))) ⨯
      (Characters.Construction.affineHopfGroupScheme R A).X).left ⟶ Spec (CommRingCat.of (S ⊗[R] A)) :=
  (Schemes.productToTensor (Spec (CommRingCat.of R))
    ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))
    (Characters.Construction.affineHopfGroupScheme R A).X).left ≫ (pullbackSpecIso R S A).hom

/-- The source coordinate comparison used by character evaluation is
its canonical tensor-product coordinate map. -/
theorem affineCharacterProductComparison :
    ((SliceCharacters.Construction.Schemes.sliceProductPullbackIso (Spec (CommRingCat.of R))
      ((Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R)))).hom.app
        (Characters.Construction.affineHopfGroupScheme R A).X).left ≫
      (AffinePullback.Construction.affineHopfPullbackIso R S A).hom.hom.hom.left =
        affineProductCoordinates R S A := by
  let T := (Spec (CommRingCat.of S)).asOver (Spec (CommRingCat.of R))
  let Y := (Characters.Construction.affineHopfGroupScheme R A).X
  let q := (Schemes.productToTensor (Spec (CommRingCat.of R)) T Y).left
  let e := Limits.pullbackSymmetry T.hom Y.hom
  have h := Schemes.sliceProductPullbackIso_eq_symmetry (Spec (CommRingCat.of R)) T Y
  change _ ≫ (e.inv ≫ (pullbackSpecIso R S A).hom) = q ≫ (pullbackSpecIso R S A).hom
  have hc := congrArg (fun f => f ≫ e.inv ≫ (pullbackSpecIso R S A).hom) h
  have he := congrArg (fun f => q ≫ f) (e.hom_inv_id_assoc (pullbackSpecIso R S A).hom)
  exact hc.trans ((Category.assoc q e.hom _).trans he)

/-- A change of test algebra acts on affine product coordinates by the
ordinary tensor product of the algebra map and the identity. -/
theorem affineProductCoordinates_natural
    (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T) :
    (Limits.prod.map
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)
      (𝟙 (Characters.Construction.affineHopfGroupScheme R A).X)).left ≫ affineProductCoordinates R S A =
    affineProductCoordinates R T A ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map f (AlgHom.id R A)).toRingHom) := by
  let F := algSpec (CommRingCat.of R)
  let : F.Braided := AlgebraicGeometry.braidedAlgSpec
  let X := Opposite.op (CommAlgCat.of R T)
  let Y := Opposite.op (CommAlgCat.of R S)
  let Z := Opposite.op (CommAlgCat.of R A)
  let a : X ⟶ Y := (CommAlgCat.ofHom f).op
  have h₀ := Functor.LaxMonoidal.μ_natural F a (𝟙 Z)
  have h := (congrArg (fun k : F.obj Z ⟶ F.obj Z =>
    (F.map a ⊗ₘ k) ≫ Functor.LaxMonoidal.μ F Y Z) (F.map_id Z)).symm.trans h₀
  have hn := Schemes.productToTensor_natural (Spec (CommRingCat.of R)) (F.map a) (𝟙 (F.obj Z))
  have hc : Limits.prod.map (F.map a) (𝟙 (F.obj Z)) ≫
      Schemes.productToTensor (Spec (CommRingCat.of R)) (F.obj Y) (F.obj Z) ≫
        Functor.LaxMonoidal.μ F Y Z =
    Schemes.productToTensor (Spec (CommRingCat.of R)) (F.obj X) (F.obj Z) ≫
      Functor.LaxMonoidal.μ F X Z ≫ F.map (a ⊗ₘ 𝟙 Z) := by
    rw [← Category.assoc, hn, Category.assoc, h]
  exact congrArg (fun k => k.left) hc

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineProduct
