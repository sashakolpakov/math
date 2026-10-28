import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.GroupIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalLevel

/-! # Monomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Monomorphisms

noncomputable section

/-! Finite group monomorphisms become isomorphisms whenever source and
target have the same finite constant group presentation. This criterion
does not require the morphism to preserve a chosen presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace FiniteGroupIso

theorem isIso_of_conjugate {C : Type*} [Category C] {X Y P : C}
    (eX : X ≅ P) (eY : Y ≅ P) (m : X ⟶ Y)
    (h : IsIso (eX.inv ≫ m ≫ eY.hom)) : IsIso m := by
  let : IsIso (eX.inv ≫ m ≫ eY.hom) := h
  let : IsIso (m ≫ eY.hom) := IsIso.of_isIso_comp_left eX.inv (m ≫ eY.hom)
  exact IsIso.of_isIso_comp_right m eY.hom

theorem isIso_of_postcomp {C : Type*} [Category C] {X Y Z : C}
    (m : X ⟶ Y) (e : Y ≅ Z) (h : IsIso (m ≫ e.hom)) : IsIso m := by
  let : IsIso (m ≫ e.hom) := h
  exact IsIso.of_isIso_comp_right m e.hom

variable {S : Scheme.{0}} {G : Type} [Group G] [Finite G]

theorem isIso_of_mono_constant_presentations {X Y : Over S} [GrpObj X] [GrpObj Y]
    (m : Grp.mk X ⟶ Grp.mk Y) (hm : Mono m.hom.hom)
    (eX : yonedaGrpObj X ≅ HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G)
    (eY : yonedaGrpObj Y ≅ HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G) : IsIso m := by
  let : Mono m.hom.hom := hm
  let α := eX.inv ≫ yonedaGrp.map m ≫ eY.hom
  have hinj (T : Over S) : Function.Injective (α.app (.op T)) := by
    intro x y h
    have h' : (eX.inv.app (.op T) x) ≫ m.hom.hom =
        (eX.inv.app (.op T) y) ≫ m.hom.hom :=
      ((eY.app (.op T)).groupIsoToMulEquiv.injective h)
    exact ((eX.app (.op T)).groupIsoToMulEquiv.symm.injective
      ((cancel_mono m.hom.hom).mp h'))
  let : IsIso (yonedaGrp.map m) :=
    isIso_of_conjugate eX eY (yonedaGrp.map m) (GroupIso.FiniteGroupIso.isIso_of_injective_card_eq α hinj rfl)
  exact isIso_of_reflects_iso m yonedaGrp

end FiniteGroupIso

namespace LevelCover

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem frameLevelMap_isIso_of_relative_split [NeZero N] (T : Over S)
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) (β : (A.pullback T.hom).FullLevel N) :
    IsIso (UniversalFrames.LevelCover.frameLevelMap A T f) := by
  let α := UniversalFrames.LevelCover.frameLevelMap A T f ≫ β.inv
  have hinj (U : Over T.left) : Function.Injective (α.app (.op U)) :=
    ((β.app (.op U)).groupIsoToMulEquiv.symm.injective).comp
      (Frame.GroupScheme.LevelCover.frameLevelMap_injective A T f U)
  exact FiniteGroupIso.isIso_of_postcomp (UniversalFrames.LevelCover.frameLevelMap A T f) β.symm
    (GroupIso.FiniteGroupIso.isIso_of_injective_card_eq α hinj rfl)

variable {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

def fullFrameInclusion [NeZero N] : Frame.Locus.LevelCover.fullFrameScheme A p (N := N) ⟶ Level.Cover.LevelCover.frameScheme A N :=
  Over.homMk (Frame.Locus.LevelCover.fullFrameOpen A p).ι rfl

/-- The original coefficient map at the full-frame inclusion is
invertible, independently of the constructed presentation used to prove
existence of a level there. -/
theorem fullFrameLevelMap_isIso [NeZero N] :
    IsIso (UniversalFrames.LevelCover.frameLevelMap A (Frame.Locus.LevelCover.fullFrameScheme A p) (fullFrameInclusion A p (N := N))) :=
  frameLevelMap_isIso_of_relative_split A _ _ (UniversalLevel.LevelCover.universalFullLevel A p)

/-- The canonical universal level is the original coefficient map. -/
def canonicalFullFrameLevel [NeZero N] :
    (A.pullback (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom).FullLevel N := by
  let : IsIso (UniversalFrames.LevelCover.frameLevelMap A (Frame.Locus.LevelCover.fullFrameScheme A p) (fullFrameInclusion A p (N := N))) :=
    fullFrameLevelMap_isIso A p
  exact asIso (UniversalFrames.LevelCover.frameLevelMap A _ (fullFrameInclusion A p))

theorem canonicalFullFrameLevel_classifying [NeZero N] :
    IndependentFrames.LevelCover.frameOfRelativeLevel A (Frame.Locus.LevelCover.fullFrameScheme A p) (canonicalFullFrameLevel A p (N := N)) =
      fullFrameInclusion A p :=
  (IndependentFrames.LevelCover.relativeFramePointsEquiv A _).left_inv _

end LevelCover

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Monomorphisms
