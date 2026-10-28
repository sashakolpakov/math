import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelSections

/-! # Section Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SectionPullback

noncomputable section

section

/-! Pullback of group-valued sections as an actual group homomorphism.
Its projection formula detects equality under an epimorphic base cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} (A : Over S) [GrpObj A] (u : T ⟶ S)

def groupSectionPullback : (Over.mk (𝟙 S) ⟶ A) →*
    (Over.mk (𝟙 T) ⟶ (Over.pullback u).obj A) :=
  (Family.PointEq.FamilyPointTransport.sectionPointEquiv A u).toMonoidHom.comp
    (((yonedaGrpObj A).map (Over.homMk u (Category.comp_id u) : Over.mk u ⟶ Over.mk (𝟙 S)).op).hom)

theorem groupSectionPullback_fst (z : Over.mk (𝟙 S) ⟶ A) :
    (groupSectionPullback A u z).left ≫ pullback.fst A.hom u = u ≫ z.left := by
  rw [groupSectionPullback, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Family.PointEq.FamilyPointTransport.sectionPointEquiv_left]
  exact Family.PointBaseChange.FamilyPointTransport.liftPoint_fst _ _ _ _

theorem groupSectionPullback_injective [Epi u] : Function.Injective (groupSectionPullback A u) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply (cancel_epi u).mp
  exact (groupSectionPullback_fst A u x).symm.trans
    ((congrArg (fun z => z.left ≫ pullback.fst A.hom u) h).trans (groupSectionPullback_fst A u y))

theorem fullLevelSection_pullback {g N : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (level : B.FullLevel N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    groupSectionPullback B.scheme u (LevelSections.fullLevelSection level c) = LevelSections.fullLevelSection (level.pullback u) c := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (groupSectionPullback_fst B.scheme u _).trans (LevelSections.fullLevelSection_pullback_fst level u c).symm
  · exact (groupSectionPullback B.scheme u _).w.trans (LevelSections.fullLevelSection (level.pullback u) c).w.symm

def fullLevelSectionHom {g N : ℕ} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (level : B.FullLevel N) :
    Multiplicative (Fin (2 * g) → ZMod N) →* (Over.mk (𝟙 S) ⟶ B.scheme) :=
  (B.torsionPoints N (Over.mk (𝟙 S))).subtype.comp
    ((level.hom.app (.op (Over.mk (𝟙 S)))).hom.comp (LocallyConstant.constMonoidHom (X := S)))

theorem fullLevelSectionHom_apply {g N : ℕ} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (level : B.FullLevel N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) : fullLevelSectionHom level c = LevelSections.fullLevelSection level c := rfl

end

/-! Actual sections recovering a full level on an epimorphic base cover
satisfy the group and torsion identities on the original base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {g N : ℕ} {S T : Scheme.{0}} (u : T ⟶ S) [Epi u]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (β : (A.pullback u).FullLevel N)
    (z : Multiplicative (Fin (2 * g) → ZMod N) → (Over.mk (𝟙 S) ⟶ A.scheme))
    (hz : ∀ c, groupSectionPullback A.scheme u (z c) = LevelSections.fullLevelSection β c)

def torsionSectionsOfPullback :
    Multiplicative (Fin (2 * g) → ZMod N) →* A.torsionPoints N (Over.mk (𝟙 S)) where
  toFun c := ⟨z c, by
    change (z c) ^ N = 1
    apply groupSectionPullback_injective A.scheme u
    rw [map_pow, hz, map_one]
    exact (β.hom.app (.op (Over.mk (𝟙 T))) (LocallyConstant.const T c)).property⟩
  map_one' := by
    apply Subtype.ext
    change z 1 = 1
    apply groupSectionPullback_injective A.scheme u
    rw [hz, map_one]
    exact (fullLevelSectionHom β).map_one
  map_mul' c d := by
    apply Subtype.ext
    change z (c * d) = z c * z d
    apply groupSectionPullback_injective A.scheme u
    rw [hz, map_mul, hz, hz]
    exact (fullLevelSectionHom β).map_mul c d

theorem torsionSectionsOfPullback_val (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    (torsionSectionsOfPullback u A β z hz c).val = z c := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SectionPullback
