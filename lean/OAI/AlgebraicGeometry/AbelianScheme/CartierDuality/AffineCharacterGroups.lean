import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterMultiplicationMul
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupMap
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupPoint
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineSheafIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroups

/-! # Affine Character Groups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterGroups

noncomputable section

/-!
# CartierDuality: compatibility of affine characters with native group laws
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Coalgebra
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction

variable (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The affine Laurent-coordinate model of the multiplicative group is commutative. -/
instance multiplicativeGroupScheme_commutative : IsCommMonObj (Characters.Construction.multiplicativeGroupScheme R).X :=
  inferInstanceAs (IsCommMonObj
    ((Spec (CommRingCat.of (Characters.Construction.MultiplicativeGroupCoordinate R))).asOver (Spec (CommRingCat.of R))))

/-- Products of group-like elements correspond to convolution products
of the associated Laurent-algebra homomorphisms. -/
theorem groupLikeHopfCharacter_mul (z w : GroupLike R A) :
    WithConv.toConv (Characters.Construction.groupLikeEquivHopfCharacters R A (z * w)).toAlgHom =
      WithConv.toConv (Characters.Construction.groupLikeEquivHopfCharacters R A z).toAlgHom *
        WithConv.toConv (Characters.Construction.groupLikeEquivHopfCharacters R A w).toAlgHom := by
  apply WithConv.ofConv_injective
  apply MonoidAlgebra.algHom_ext'
  · apply MonoidHom.ext_mint
    let f := WithConv.toConv (Characters.Construction.groupLikeEquivHopfCharacters R A z).toAlgHom
    let g := WithConv.toConv (Characters.Construction.groupLikeEquivHopfCharacters R A w).toAlgHom
    have hm := MonoidAlgebra.convMul_algHom_single_one f g (Multiplicative.ofAdd 1)
    have hz := Characters.Construction.groupLikeEquivHopfCharacters_generator R A z
    have hw := Characters.Construction.groupLikeEquivHopfCharacters_generator R A w
    exact (Characters.Construction.groupLikeEquivHopfCharacters_generator R A (z * w)).trans
      ((congrArg₂ (fun a b : A => a * b) hz.symm hw.symm).trans hm.symm)
  · exact Subsingleton.elim _ _

/-- The scheme character has the Spec point corresponding to its
Laurent-algebra homomorphism. -/
theorem groupLikeSchemeCharacter_hom (z : GroupLike R A) :
    (Characters.Construction.groupLikeEquivSchemeCharacters R A z).hom.hom =
      Spec.mapMulEquiv (R := R) (S := Characters.Construction.MultiplicativeGroupCoordinate R) (T := A)
        (WithConv.toConv (Characters.Construction.groupLikeEquivHopfCharacters R A z).toAlgHom) := by
  apply Over.OverMorphism.ext
  rfl

/-- The group-like character equivalence respects the actual native
group law on group-scheme homomorphisms into the multiplicative group. -/
theorem groupLikeSchemeCharacter_mul (z w : GroupLike R A) :
    Characters.Construction.groupLikeEquivSchemeCharacters R A (z * w) =
      Characters.Construction.groupLikeEquivSchemeCharacters R A z * Characters.Construction.groupLikeEquivSchemeCharacters R A w := by
  apply Grp.hom_ext
  change (Characters.Construction.groupLikeEquivSchemeCharacters R A (z * w)).hom.hom =
    (Characters.Construction.groupLikeEquivSchemeCharacters R A z).hom.hom * (Characters.Construction.groupLikeEquivSchemeCharacters R A w).hom.hom
  rw [groupLikeSchemeCharacter_hom, groupLikeSchemeCharacter_hom, groupLikeSchemeCharacter_hom]
  exact (congrArg
    (Spec.mapMulEquiv (R := R) (S := Characters.Construction.MultiplicativeGroupCoordinate R) (T := A))
      (groupLikeHopfCharacter_mul R A z w)).trans (map_mul _ _ _)

/-- Group-like elements and native affine group-scheme characters are
equivalent as groups, with no change to their previously proved correspondence. -/
def groupLikeMulEquivSchemeCharacters :
    GroupLike R A ≃* (Characters.Construction.affineHopfGroupScheme R A ⟶ Characters.Construction.multiplicativeGroupScheme R) where
  toEquiv := Characters.Construction.groupLikeEquivSchemeCharacters R A
  map_mul' := groupLikeSchemeCharacter_mul R A

variable (B : Type u) [CommRing B] [Algebra R B]

/-- The affine-coordinate character/section equivalence respects
the native pointwise group laws throughout all pullback comparisons. -/
def affineGroupCharacterSectionsMulEquiv :
    (Characters.Construction.affineHopfGroupScheme B (B ⊗[R] A) ⟶ Characters.Construction.multiplicativeGroupScheme B) ≃*
      (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj.obj
        (Opposite.op ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))) :=
  (CharacterMultiplicationMul.Construction.CharacterMultiplication.homCongrMulEquiv (AffinePullback.Construction.affineHopfPullbackIso R B A).symm
    (AffinePullback.Construction.Schemes.multiplicativeGroupOverSpecIso B).symm).trans
      (CharacterMultiplicationMul.Construction.Schemes.testCharacterMulEquiv (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
        ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))).symm

/-- The group-valued refinement uses the original affine character correspondence. -/
theorem affineGroupCharacterSectionsMulEquiv_apply
    (χ : Characters.Construction.affineHopfGroupScheme B (B ⊗[R] A) ⟶ Characters.Construction.multiplicativeGroupScheme B) :
    affineGroupCharacterSectionsMulEquiv R A B χ = AffinePullback.Construction.affineGroupCharacterSectionsEquiv R B A χ :=
  rfl

/-- The affine group-like character section construction preserves multiplication. -/
theorem affineGroupLikeSection_mul (z w : GroupLike B (B ⊗[R] A)) :
    AffineCharacterValues.Construction.affineGroupLikeSection R B A (z * w) =
      AffineCharacterValues.Construction.affineGroupLikeSection R B A z * AffineCharacterValues.Construction.affineGroupLikeSection R B A w := by
  exact ((groupLikeMulEquivSchemeCharacters B (B ⊗[R] A)).trans
    (affineGroupCharacterSectionsMulEquiv R A B)).map_mul z w

/-- The multiplicative Spec point correspondence uses the same
underlying affine point map as the original algebra/Spec equivalence. -/
theorem specMapMulEquiv_eq_affinePoint (f : A →ₐ[R] B) :
    Spec.mapMulEquiv (R := R) (S := A) (T := B) (WithConv.toConv f) =
      (Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm f := by
  apply Over.OverMorphism.ext
  rfl

/-- The inverse multiplicative Spec correspondence is the original
affine point algebra map with its convolution group structure. -/
theorem specMapMulEquiv_symm_eq_affinePoint
    (f : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R))) :
    (Spec.mapMulEquiv (R := R) (S := A) (T := B)).symm f =
      WithConv.toConv (Characters.Construction.affineSchemePointsEquivAlgHom R A B f) := by
  apply (Spec.mapMulEquiv (R := R) (S := A) (T := B)).injective
  exact ((Spec.mapMulEquiv (R := R) (S := A) (T := B)).apply_symm_apply f).trans
    ((specMapMulEquiv_eq_affinePoint R A B _).trans
      ((Characters.Construction.affineSchemePointsEquivAlgHom R A B).symm_apply_apply f)).symm

variable [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]

local instance e56AffineCharacterGroupsDualRing : CommRing (DualAlgebra.Construction.DualCoordinate R A) :=
  LinearMap.convCommRing
local instance e56AffineCharacterGroupsDualAlgebra : Algebra R (DualAlgebra.Construction.DualCoordinate R A) :=
  LinearMap.convAlgebra

/-- The dual-coordinate scheme points and actual affine character
sections are equivalent as groups. -/
def affineCartierSectionsMulEquiv :
    ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))) ≃*
      (CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)).obj.obj
        (Opposite.op ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))) :=
  (Spec.mapMulEquiv (R := R) (S := DualAlgebra.Construction.DualCoordinate R A) (T := B)).symm.trans
    ((CharacterGroups.Construction.affineDualPointsMulEquivCharacters R B A).trans
      ((groupLikeMulEquivSchemeCharacters B (B ⊗[R] A)).trans
        (affineGroupCharacterSectionsMulEquiv R A B)))

/-- The multiplicative affine correspondence has the original
pointwise affine character-section formula. -/
theorem affineCartierSectionsMulEquiv_apply
    (f : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))) :
    affineCartierSectionsMulEquiv R A B f = AffineCharacterValues.Construction.affineGroupLikeSection R B A
      (DualAlgebra.Construction.affineDualPointsEquivCharacters R B A (Characters.Construction.affineSchemePointsEquivAlgHom R (DualAlgebra.Construction.DualCoordinate R A) B f)) := by
  have h := specMapMulEquiv_symm_eq_affinePoint R (DualAlgebra.Construction.DualCoordinate R A) B f
  exact congrArg
    (fun g => AffineCharacterValues.Construction.affineGroupLikeSection R B A (CharacterGroups.Construction.affineDualPointsMulEquivCharacters R B A g)) h

/-- The canonical sheaf comparison agrees with the native group
isomorphism on every affine test scheme. -/
theorem affineCartierCharacterMap_apply_mulEquiv
    (f : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))) :
    (CharacterMap.Construction.affineCartierCharacterMap R A).app
      (Opposite.op ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))) (ULift.up f) =
        affineCartierSectionsMulEquiv R A B f :=
  (AffineSheafIso.Construction.affineCartierCharacterMap_apply_affine R B A f).trans
    (affineCartierSectionsMulEquiv_apply R A B f).symm

/-- The canonical character-sheaf map preserves multiplication on
affine test schemes. -/
theorem affineCartierCharacterMap_mul_affine
    (f g : (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))) :
    (CharacterMap.Construction.affineCartierCharacterMap R A).app
        (Opposite.op ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))) (ULift.up (f * g)) =
      (CharacterMap.Construction.affineCartierCharacterMap R A).app
        (Opposite.op ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))) (ULift.up f) *
      (CharacterMap.Construction.affineCartierCharacterMap R A).app
        (Opposite.op ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R)))) (ULift.up g) := by
  rw [affineCartierCharacterMap_apply_mulEquiv, affineCartierCharacterMap_apply_mulEquiv,
    affineCartierCharacterMap_apply_mulEquiv]
  exact (affineCartierSectionsMulEquiv R A B).map_mul f g

/-- The canonical affine Cartier character-sheaf map preserves
multiplication on every test scheme over the affine base. -/
theorem affineCartierCharacterMap_mul
    (T : Over (Spec (CommRingCat.of R)))
    (f g : T ⟶ (Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R))) :
    (CharacterMap.Construction.affineCartierCharacterMap R A).app (Opposite.op T) (ULift.up (f * g)) =
      (CharacterMap.Construction.affineCartierCharacterMap R A).app (Opposite.op T) (ULift.up f) *
        (CharacterMap.Construction.affineCartierCharacterMap R A).app (Opposite.op T) (ULift.up g) := by
  apply GroupMap.Construction.Schemes.characterMap_mul_of_affine (CommRingCat.of R) (Characters.Construction.affineHopfGroupScheme R A)
    ((Spec (CommRingCat.of (DualAlgebra.Construction.DualCoordinate R A))).asOver (Spec (CommRingCat.of R)))
    (CharacterMap.Construction.affineCartierCharacterSheafMap R A)
  intro C f g
  exact affineCartierCharacterMap_mul_affine R A C f g

/-- The affine Hopf-algebra dual represents the actual character
groups naturally on every scheme over the affine base. -/
def affineCartierGroupPointIso :
    yonedaGrp.obj (Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A)) ≅
      CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A) ⋙
        forget₂ CommGrpCat GrpCat := by
  let e₀ := @asIso _ _ _ _ (CharacterMap.Construction.affineCartierCharacterSheafMap R A)
    (AffineSheafIso.Construction.affineCartierCharacterSheafMap_isIso R A)
  let e : CharacterFunctor.Construction.Schemes.pointSheaf (Spec (CommRingCat.of R))
      (Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A)).X ≅
        CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A) := e₀
  exact CharacterGroupPoint.Construction.Schemes.characterGroupPointIso (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
    (Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A)) e (affineCartierCharacterMap_mul R A)

/-- The group-valued affine representation retains the original
canonical universal-character map exactly. -/
theorem affineCartierGroupPointIso_character (T : Over (Spec (CommRingCat.of R)))
    (f : T ⟶ (Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A)).X) :
    CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
      (Opposite.op T) ((affineCartierGroupPointIso R A).hom.app (Opposite.op T) f) =
        (CharacterMap.Construction.affineCartierCharacterMap R A).app (Opposite.op T) (ULift.up f) := by
  let e₀ := @asIso _ _ _ _ (CharacterMap.Construction.affineCartierCharacterSheafMap R A)
    (AffineSheafIso.Construction.affineCartierCharacterSheafMap_isIso R A)
  let e : CharacterFunctor.Construction.Schemes.pointSheaf (Spec (CommRingCat.of R))
      (Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A)).X ≅
        CharacterSheaf.Construction.Schemes.characterSheaf (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A) := e₀
  exact CharacterGroupPoint.Construction.Schemes.characterGroupPointIso_character (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)
    (Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A)) e (affineCartierCharacterMap_mul R A) T f

/-- Any native group representative of the affine character sheaf is
isomorphic, as a group scheme, to the constructed dual Hopf spectrum. -/
def characterRepresentativeAffineIso
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (CommRingCat.of R)) (Characters.Construction.affineHopfGroupScheme R A)) :
    D.dual ≅ Characters.Construction.affineHopfGroupScheme R (DualAlgebra.Construction.DualCoordinate R A) :=
  yonedaGrpFullyFaithful.preimageIso (D.pointsIso ≪≫ (affineCartierGroupPointIso R A).symm)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineCharacterGroups
