import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDualGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback

/-! # Dual Homomorphism -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.DualHomomorphism

noncomputable section

/-! Pullback of line bundles induces homomorphisms for the Picard-derived dual groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {g h : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

def homogeneousPicardPullbackGroupPresheaf :
    HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf B ⟶ HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf A where
  app T := CommGrpCat.ofHom
    { toFun := (HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf A B f).app T
      map_one' := Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (T.unop ◁ f).left)
      map_mul' q r := Subtype.ext (SchemePullback.Construction.pullbackClass_mul (T.unop ◁ f).left q.val r.val) }
  naturality {T U} t := by
    ext q
    exact (HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf A B f).naturality_apply t q

def homogeneousPicardPullbackHom (T : Over S) :
    B.homogeneousPicardSheaf.obj.obj (op T) →* A.homogeneousPicardSheaf.obj.obj (op T) :=
  GroupSheafMaps.Construction.picardTypeSheafifyMapHom (homogeneousPicardPullbackGroupPresheaf A B f) (op T)

theorem homogeneousPicardPullbackHom_apply (T : Over S)
    (q : B.homogeneousPicardSheaf.obj.obj (op T)) :
    homogeneousPicardPullbackHom A B f T q =
      (HomogeneousPullback.Construction.homogeneousPicardPullback A B f).hom.app (op T) q :=
  GroupSheafMaps.Construction.picardTypeSheafifyMapHom_apply (homogeneousPicardPullbackGroupPresheaf A B f) (op T) q

variable {A B} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

def dualPicardPullbackPoints (T : Over S) :
    letI := CanonicalDualGroup.Construction.dualPicardGroup D
    letI := CanonicalDualGroup.Construction.dualPicardGroup E
    (T ⟶ E.abelian.scheme) →* (T ⟶ D.abelian.scheme) :=
  letI := CanonicalDualGroup.Construction.dualPicardGroup D
  letI := CanonicalDualGroup.Construction.dualPicardGroup E
  (CanonicalDualGroup.Construction.dualPicardGroupHomEquiv D T).symm.toMonoidHom.comp
    ((homogeneousPicardPullbackHom A B f T).comp (CanonicalDualGroup.Construction.dualPicardGroupHomEquiv E T).toMonoidHom)

theorem dualPicardPullbackPoints_apply (T : Over S) (x : T ⟶ E.abelian.scheme) :
    dualPicardPullbackPoints f D E T x = x ≫ DualPullback.Construction.dualPicardPullback D E f := by
  let := CanonicalDualGroup.Construction.dualPicardGroup D
  let := CanonicalDualGroup.Construction.dualPicardGroup E
  apply (CanonicalDualGroup.Construction.dualPicardGroupHomEquiv D T).injective
  change CanonicalDualGroup.Construction.dualPicardGroupHomEquiv D T ((CanonicalDualGroup.Construction.dualPicardGroupHomEquiv D T).symm
      (homogeneousPicardPullbackHom A B f T (CanonicalDualGroup.Construction.dualPicardGroupHomEquiv E T x))) = _
  rw [MulEquiv.apply_symm_apply, homogeneousPicardPullbackHom_apply,
    CanonicalDualGroup.Construction.dualPicardGroupHomEquiv_apply, CanonicalDualGroup.Construction.dualPicardGroupHomEquiv_apply]
  exact (DualPullback.Construction.dualPicardPullback_representation D E f x).symm

theorem dualPicardPullback_isMonHom :
    letI := CanonicalDualGroup.Construction.dualPicardGroup D
    letI := CanonicalDualGroup.Construction.dualPicardGroup E
    IsMonHom (DualPullback.Construction.dualPicardPullback D E f) := by
  let := CanonicalDualGroup.Construction.dualPicardGroup D
  let := CanonicalDualGroup.Construction.dualPicardGroup E
  constructor
  · have e := (dualPicardPullbackPoints f D E (𝟙_ (Over S))).map_one
    rw [dualPicardPullbackPoints_apply] at e
    simpa only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp] using e
  · have e := (dualPicardPullbackPoints f D E (E.abelian.scheme ⊗ E.abelian.scheme)).map_mul
      (fst E.abelian.scheme E.abelian.scheme) (snd E.abelian.scheme E.abelian.scheme)
    rw [dualPicardPullbackPoints_apply, dualPicardPullbackPoints_apply,
      dualPicardPullbackPoints_apply] at e
    change (lift (fst E.abelian.scheme E.abelian.scheme) (snd E.abelian.scheme E.abelian.scheme) ≫
        MonObj.mul) ≫ DualPullback.Construction.dualPicardPullback D E f =
      lift (fst E.abelian.scheme E.abelian.scheme ≫ DualPullback.Construction.dualPicardPullback D E f)
        (snd E.abelian.scheme E.abelian.scheme ≫ DualPullback.Construction.dualPicardPullback D E f) ≫ MonObj.mul at e
    have ht : lift (fst E.abelian.scheme E.abelian.scheme ≫ DualPullback.Construction.dualPicardPullback D E f)
        (snd E.abelian.scheme E.abelian.scheme ≫ DualPullback.Construction.dualPicardPullback D E f) =
        (DualPullback.Construction.dualPicardPullback D E f ⊗ₘ DualPullback.Construction.dualPicardPullback D E f) := by
      ext <;> simp only [lift_fst, tensorHom_fst, lift_snd, tensorHom_snd]
    rw [ht] at e
    simpa only [lift_fst_snd, Category.id_comp] using e

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.DualHomomorphism
