import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Yoneda

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Naturality.Construction

noncomputable section

/-!
# CartierDuality: naturality of affine Cartier character representation

The maps on group-like elements are identified with the ordinary tensor
base-change maps, so the pointwise representation does not leave the
transition maps unspecified.
-/

open _root_.Module TensorProduct _root_.CategoryTheory

universe u v w w'

section LinearNaturality

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable {S : Type w} [CommRing S] [Algebra R S]
variable {T : Type w'} [CommRing T] [Algebra R T]

/-- Evaluation against an extended dual functional is natural in the
coefficient algebra. -/
theorem scalarExtension_dual_map (f : S →ₐ[R] T) (g : Module.Dual R M)
    (z : S ⊗[R] M) :
    g.baseChange T (TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[R] M) z) =
      f (g.baseChange S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x => simp [Algebra.smul_def]
  | add a b ha hb => simp [ha, hb]

end LinearNaturality

section CharacterNaturality

variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]
variable {S : Type w} [CommRing S] [Algebra R S]
variable {T : Type w'} [CommRing T] [Algebra R T]

/-- Base change of an affine character. The next theorem verifies that its
underlying element is the canonical tensor base change. -/
def changeRingGroupLike (f : S →ₐ[R] T) (z : GroupLike S (S ⊗[R] A)) :
    GroupLike T (T ⊗[R] A) :=
  DualAlgebra.Construction.affineDualPointsEquivCharacters R T A
    (f.comp ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm z))

theorem changeRingGroupLike_val (f : S →ₐ[R] T) (z : GroupLike S (S ⊗[R] A)) :
    (changeRingGroupLike R A f z).val =
      TensorProduct.map f.toLinearMap (LinearMap.id : A →ₗ[R] A) z.val := by
  apply DualAlgebra.Construction.scalarExtension_dual_ext R A T
  intro g
  calc
    g.baseChange T (changeRingGroupLike R A f z).val =
        (DualAlgebra.Construction.affineDualPointsEquivCharacters R T A).symm
          (changeRingGroupLike R A f z) (WithConv.toConv g) :=
      (DualAlgebra.Construction.affineDualPointsEquivCharacters_symm_apply_dual R T A _ _).symm
    _ = f ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm z (WithConv.toConv g)) := by
      rw [changeRingGroupLike, Equiv.symm_apply_apply]
      rfl
    _ = f (g.baseChange S z.val) := by
      rw [DualAlgebra.Construction.affineDualPointsEquivCharacters_symm_apply_dual]
    _ = g.baseChange T
        (TensorProduct.map f.toLinearMap (LinearMap.id : A →ₗ[R] A) z.val) :=
      (scalarExtension_dual_map R A f g z.val).symm

theorem changeRingGroupLike_one (f : S →ₐ[R] T) :
    changeRingGroupLike R A f 1 = 1 := by
  apply GroupLike.val_injective
  rw [changeRingGroupLike_val]
  change (Algebra.TensorProduct.map f (AlgHom.id R A)) 1 = 1
  exact (Algebra.TensorProduct.map f (AlgHom.id R A)).map_one

theorem changeRingGroupLike_mul (f : S →ₐ[R] T)
    (z z' : GroupLike S (S ⊗[R] A)) :
    changeRingGroupLike R A f (z * z') =
      changeRingGroupLike R A f z * changeRingGroupLike R A f z' := by
  apply GroupLike.val_injective
  rw [changeRingGroupLike_val]
  change TensorProduct.map f.toLinearMap (LinearMap.id : A →ₗ[R] A) (z.val * z'.val) =
    (changeRingGroupLike R A f z).val * (changeRingGroupLike R A f z').val
  rw [changeRingGroupLike_val, changeRingGroupLike_val]
  exact (Algebra.TensorProduct.map f (AlgHom.id R A)).map_mul z.val z'.val

/-- The canonical change-of-ring map on character groups. -/
def changeRingGroupLikeHom (f : S →ₐ[R] T) :
    GroupLike S (S ⊗[R] A) →* GroupLike T (T ⊗[R] A) where
  toFun := changeRingGroupLike R A f
  map_one' := changeRingGroupLike_one R A f
  map_mul' := changeRingGroupLike_mul R A f

@[simp]
theorem changeRingGroupLike_id (z : GroupLike S (S ⊗[R] A)) :
    changeRingGroupLike R A (AlgHom.id R S) z = z := by
  simp [changeRingGroupLike]

theorem changeRingGroupLike_comp
    {U : Type*} [CommRing U] [Algebra R U]
    (f : S →ₐ[R] T) (g : T →ₐ[R] U) (z : GroupLike S (S ⊗[R] A)) :
    changeRingGroupLike R A g (changeRingGroupLike R A f z) =
      changeRingGroupLike R A (g.comp f) z := by
  simp [changeRingGroupLike, AlgHom.comp_assoc]

end CharacterNaturality

section UniversalCharacter

variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

/-- The universal affine character is the group-like coevaluation element
corresponding to the identity point of the dual coordinate algebra. -/
def universalAffineCharacter :
    GroupLike (DualAlgebra.Construction.DualCoordinate R A) (DualAlgebra.Construction.DualCoordinate R A ⊗[R] A) :=
  DualAlgebra.Construction.affineDualPointsEquivCharacters R (DualAlgebra.Construction.DualCoordinate R A) A
    (AlgHom.id R (DualAlgebra.Construction.DualCoordinate R A))

/-- Contracting the universal element against a dual functional recovers
that functional. This is the coefficient identity of the evaluation pairing. -/
theorem universalAffineCharacter_dualValue (f : DualAlgebra.Construction.DualCoordinate R A) :
    f.ofConv.baseChange (DualAlgebra.Construction.DualCoordinate R A) (universalAffineCharacter R A).val = f := by
  calc
    _ = (DualAlgebra.Construction.affineDualPointsEquivCharacters R (DualAlgebra.Construction.DualCoordinate R A) A).symm
        (universalAffineCharacter R A) f :=
      (DualAlgebra.Construction.affineDualPointsEquivCharacters_symm_apply_dual R (DualAlgebra.Construction.DualCoordinate R A) A _ _).symm
    _ = f := by
      rw [universalAffineCharacter, Equiv.symm_apply_apply]
      rfl

/-- Every affine character is obtained from the universal one by ordinary
tensor base change along its dual point. -/
theorem universalAffineCharacter_baseChange
    {S : Type w} [CommRing S] [Algebra R S]
    (f : DualAlgebra.Construction.DualCoordinate R A →ₐ[R] S) :
    (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A f).val =
      TensorProduct.map f.toLinearMap (LinearMap.id : A →ₗ[R] A)
        (universalAffineCharacter R A).val := by
  have h := changeRingGroupLike_val R A f (universalAffineCharacter R A)
  simpa only [changeRingGroupLike, universalAffineCharacter, Equiv.symm_apply_apply,
    AlgHom.comp_id] using h

end UniversalCharacter

variable (R A : Type u) [CommRing R] [CommRing A]
variable [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

/-- The affine character functor, with its verified tensor base-change maps. -/
def affineCharacterFunctor : CommAlgCat R ⥤ Type u where
  obj S := GroupLike S (S ⊗[R] A)
  map f := ↾(changeRingGroupLike R A f.hom)
  map_id S := by
    ext z
    exact congrArg GroupLike.val (changeRingGroupLike_id R A z)
  map_comp f g := by
    ext z
    exact congrArg GroupLike.val (changeRingGroupLike_comp R A f.hom g.hom z).symm

/-- The representation of affine characters is natural in the test algebra. -/
def affineCharacterRepresentation :
    coyoneda.obj (Opposite.op (CommAlgCat.of R (DualAlgebra.Construction.DualCoordinate R A))) ≅
      affineCharacterFunctor R A :=
  NatIso.ofComponents
    (fun S => ((Equiv.mk
      (fun h : CommAlgCat.of R (DualAlgebra.Construction.DualCoordinate R A) ⟶ S => h.hom)
      (fun h => CommAlgCat.ofHom h)
      (fun _ => rfl) (fun _ => rfl)).trans
        (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A)).toIso)
    (by
      intro S T f
      ext h
      change DualAlgebra.Construction.affineDualPointsEquivCharacters R T A (f.hom.comp h.hom) =
        DualAlgebra.Construction.affineDualPointsEquivCharacters R T A
          (f.hom.comp ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm
            (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A h.hom)))
      rw [Equiv.symm_apply_apply])

/-- The affine character functor is represented by the constructed finite
projective dual coordinate algebra. -/
theorem affineCharacterFunctor_corepresentable :
    (affineCharacterFunctor R A).IsCorepresentable :=
  ⟨CommAlgCat.of R (DualAlgebra.Construction.DualCoordinate R A),
    ⟨Functor.corepresentableByEquiv.symm (affineCharacterRepresentation R A)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Naturality.Construction
