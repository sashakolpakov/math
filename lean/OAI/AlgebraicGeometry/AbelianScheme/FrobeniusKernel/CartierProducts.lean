import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel

/-! # Cartier Products -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierProducts.Construction

noncomputable section

/-!
Cartier duality carries an actual split product to the product of its
duals. The comparison map is restriction to the two factor inclusions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}}

def splitFirstProjection (G H : Grp (Over S)) : G ⊗ H ⟶ G :=
  Grp.homMk (fst G.X H.X)

def characterSectionsCongr {G H : Grp (Over S)} (e : G ≅ H) (T : Over S) :
    CharacterGroups.Construction.CharacterSections G T ≃ CharacterGroups.Construction.CharacterSections H T where
  toFun χ := (CharacterGroups.Construction.characterGroupRestriction e.inv).app (op T) χ
  invFun χ := (CharacterGroups.Construction.characterGroupRestriction e.hom).app (op T) χ
  left_inv χ := by
    ext U x
    change U.unop.left ⟶ G.X at x
    change χ.app U ((x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) = χ.app U x
    have h : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
      congrArg (fun f : G ⟶ G => f.hom.hom) e.hom_inv_id
    erw [Category.assoc, h, Category.comp_id]
  right_inv χ := by
    ext U x
    change U.unop.left ⟶ H.X at x
    change χ.app U ((x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) = χ.app U x
    have h : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X :=
      congrArg (fun f : H ⟶ H => f.hom.hom) e.inv_hom_id
    erw [Category.assoc, h, Category.comp_id]

/-- Every character of a product is the product of its two restrictions. -/
def splitCharacterEquiv (G H : Grp (Over S)) (T : Over S) :
    CharacterGroups.Construction.CharacterSections (G ⊗ H) T ≃ CharacterGroups.Construction.CharacterSections G T × CharacterGroups.Construction.CharacterSections H T where
  toFun χ := ((CharacterGroups.Construction.characterGroupRestriction (AnnihilatorSheaf.Construction.splitFirstInclusion G H)).app (op T) χ,
    (CharacterGroups.Construction.characterGroupRestriction (AnnihilatorSheaf.Construction.splitSecondInclusion G H)).app (op T) χ)
  invFun χ := (CharacterGroups.Construction.characterGroupRestriction (splitFirstProjection G H)).app (op T) χ.1 *
    (CharacterGroups.Construction.characterGroupRestriction (AnnihilatorSheaf.Construction.splitSecondProjection G H)).app (op T) χ.2
  left_inv χ := by
    ext U z
    change U.unop.left ⟶ (G ⊗ H).X at z
    let χU : (U.unop.left ⟶ (G ⊗ H).X) →*
      (U.unop.left ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) := (χ.app U).hom
    change χU ((z ≫ fst G.X H.X) ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X)) *
      χU ((z ≫ snd G.X H.X) ≫ lift (1 : H.X ⟶ G.X) (𝟙 H.X)) = χU z
    rw [← χU.map_mul]
    apply congrArg χU
    apply CartesianMonoidalCategory.hom_ext
    · simp only [MonObj.mul_comp, Category.assoc, lift_fst, Category.comp_id,
        MonObj.comp_one, mul_one]
    · simp only [MonObj.mul_comp, Category.assoc, lift_snd, Category.comp_id,
        MonObj.comp_one, one_mul]
  right_inv χ := by
    apply Prod.ext
    · ext U z
      change U.unop.left ⟶ G.X at z
      change χ.1.app U ((z ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X)) ≫ fst G.X H.X) *
        χ.2.app U ((z ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X)) ≫ snd G.X H.X) = χ.1.app U z
      erw [Category.assoc, Category.assoc, lift_fst, lift_snd, Category.comp_id,
        MonObj.comp_one, (χ.2.app U).hom.map_one, mul_one]
    · ext U z
      change U.unop.left ⟶ H.X at z
      change χ.1.app U ((z ≫ lift (1 : H.X ⟶ G.X) (𝟙 H.X)) ≫ fst G.X H.X) *
        χ.2.app U ((z ≫ lift (1 : H.X ⟶ G.X) (𝟙 H.X)) ≫ snd G.X H.X) = χ.2.app U z
      erw [Category.assoc, Category.assoc, lift_fst, lift_snd, Category.comp_id,
        MonObj.comp_one, (χ.1.app U).hom.map_one, one_mul]

variable {R : CommRingCat.{u}} {B G H : Grp (Over (Spec R))}
variable (e : B ≅ G ⊗ H) (P : CartierModel.Construction.CartierCoordinates R B)
variable (Q : CartierModel.Construction.CartierCoordinates R G) (V : CartierModel.Construction.CartierCoordinates R H)

def splitDualRestriction : P.dualGroup ⟶ Q.dualGroup ⊗ V.dualGroup :=
  Grp.homMk (lift (P.restriction Q (AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv)).hom.hom
    (P.restriction V (AnnihilatorSheaf.Construction.splitSecondInclusion G H ≫ e.inv)).hom.hom)

def splitDualPointsEquiv (T : Over (Spec R)) :
    (T ⟶ P.dualGroup.X) ≃ (T ⟶ (Q.dualGroup ⊗ V.dualGroup).X) :=
  (P.pointsEquiv T).toEquiv |>.trans (characterSectionsCongr e T) |>.trans
    (splitCharacterEquiv G H T) |>.trans
      (Equiv.prodCongr (Q.pointsEquiv T).toEquiv.symm (V.pointsEquiv T).toEquiv.symm) |>.trans
        { toFun := fun a => lift a.1 a.2
          invFun := fun a => (a ≫ fst _ _, a ≫ snd _ _)
          left_inv := fun a => by simp only [lift_fst, lift_snd]
          right_inv := fun a => by
            exact (comp_lift a (fst _ _) (snd _ _)).symm.trans
              ((congrArg (fun f => a ≫ f) lift_fst_snd).trans (Category.comp_id a)) }

theorem splitDualPointsEquiv_apply (T : Over (Spec R)) (a : T ⟶ P.dualGroup.X) :
    splitDualPointsEquiv e P Q V T a = a ≫ (splitDualRestriction e P Q V).hom.hom := by
  apply CartesianMonoidalCategory.hom_ext
  · change (lift _ _) ≫ fst Q.dualGroup.X V.dualGroup.X = _
    rw [lift_fst]
    change (Q.pointsEquiv T).symm
      ((CharacterGroups.Construction.characterGroupRestriction (AnnihilatorSheaf.Construction.splitFirstInclusion G H)).app (op T)
        ((CharacterGroups.Construction.characterGroupRestriction e.inv).app (op T) (P.pointsEquiv T a))) =
      (a ≫ lift _ _) ≫ fst Q.dualGroup.X V.dualGroup.X
    rw [Category.assoc, lift_fst]
    let χ : CharacterGroups.Construction.CharacterSections G T :=
      (CharacterGroups.Construction.characterGroupRestriction (AnnihilatorSheaf.Construction.splitFirstInclusion G H)).app (op T)
        ((CharacterGroups.Construction.characterGroupRestriction e.inv).app (op T) (P.pointsEquiv T a))
    have hχ : χ = Functor.whiskerLeft (Over.forget T).op
        (yonedaGrp.map (AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv)) ≫ P.pointsEquiv T a := by
      ext U x
      exact congrArg (fun z => (P.pointsEquiv T a).app U z)
        (Category.assoc x (AnnihilatorSheaf.Construction.splitFirstInclusion G H).hom.hom e.inv.hom.hom)
    exact (congrArg (Q.pointsEquiv T).symm
      (hχ.trans (P.restriction_on_characters Q (AnnihilatorSheaf.Construction.splitFirstInclusion G H ≫ e.inv) T a).symm)).trans
        ((Q.pointsEquiv T).symm_apply_apply _)
  · change (lift _ _) ≫ snd Q.dualGroup.X V.dualGroup.X = _
    rw [lift_snd]
    change (V.pointsEquiv T).symm
      ((CharacterGroups.Construction.characterGroupRestriction (AnnihilatorSheaf.Construction.splitSecondInclusion G H)).app (op T)
        ((CharacterGroups.Construction.characterGroupRestriction e.inv).app (op T) (P.pointsEquiv T a))) =
      (a ≫ lift _ _) ≫ snd Q.dualGroup.X V.dualGroup.X
    rw [Category.assoc, lift_snd]
    let χ : CharacterGroups.Construction.CharacterSections H T :=
      (CharacterGroups.Construction.characterGroupRestriction (AnnihilatorSheaf.Construction.splitSecondInclusion G H)).app (op T)
        ((CharacterGroups.Construction.characterGroupRestriction e.inv).app (op T) (P.pointsEquiv T a))
    have hχ : χ = Functor.whiskerLeft (Over.forget T).op
        (yonedaGrp.map (AnnihilatorSheaf.Construction.splitSecondInclusion G H ≫ e.inv)) ≫ P.pointsEquiv T a := by
      ext U x
      exact congrArg (fun z => (P.pointsEquiv T a).app U z)
        (Category.assoc x (AnnihilatorSheaf.Construction.splitSecondInclusion G H).hom.hom e.inv.hom.hom)
    exact (congrArg (V.pointsEquiv T).symm
      (hχ.trans (P.restriction_on_characters V (AnnihilatorSheaf.Construction.splitSecondInclusion G H ≫ e.inv) T a).symm)).trans
        ((V.pointsEquiv T).symm_apply_apply _)

instance splitDualRestriction_isIso : IsIso (splitDualRestriction e P Q V).hom.hom := by
  apply isIso_of_yoneda_map_bijective
  intro T
  have h : (fun a : T ⟶ P.dualGroup.X => a ≫ (splitDualRestriction e P Q V).hom.hom) =
      splitDualPointsEquiv e P Q V T :=
    funext (fun a => (splitDualPointsEquiv_apply e P Q V T a).symm)
  exact h ▸ (splitDualPointsEquiv e P Q V T).bijective

/-- Native product duality with its specified restriction morphism. -/
def splitDualGroupIso : P.dualGroup ≅ Q.dualGroup ⊗ V.dualGroup :=
  Grp.mkIso (asIso (splitDualRestriction e P Q V).hom.hom)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierProducts.Construction
