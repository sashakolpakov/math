import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFrames

/-! # Group Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover

noncomputable section

section

/-! Injectivity of the universal frame on all tests, proved from its
defining nonvanishing relations, without a splitting or full level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem frameTorsionHom_injective [NeZero N] (T : Over S) [Nonempty T.left]
    (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) : Function.Injective (Labels.LevelCover.frameTorsionHom A T f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro c hc
  change c = 1
  by_contra hne
  have hrel := congrArg Subtype.val hc
  rw [Labels.LevelCover.frameTorsionHom_val] at hrel
  exact Level.Cover.LevelCover.frame_relations_nonzero A N T f c.toAdd
    (fun h => hne (Multiplicative.toAdd.injective h)) hrel

theorem torsionSectionExtension_injective
    (h : Labels.LevelCover.Coefficients g N →* A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest S))
    (hind : ∀ (U : Over S), Nonempty U.left → ∀ c : Labels.LevelCover.Coefficients g N,
      A.torsionPullback N (ConstantSectionsOn.ConstantSections.toBase U) (h c) = 1 → c = 1) (T : Over S) :
    Function.Injective ((UniversalFrames.LevelCover.torsionSectionExtension A h).app (.op T)) := by
  let h' : Labels.LevelCover.Coefficients g N →* (ConstantSectionsOn.ConstantSections.baseTest S ⟶ A.torsionScheme N) :=
    ((A.torsionSchemeYonedaIso N).inv.app (.op (ConstantSectionsOn.ConstantSections.baseTest S))).hom.comp h
  have hinj : Function.Injective (ConstantSectionsOn.ConstantSections.extendHom h' T) := by
    apply ConstantSectionsOn.ConstantSections.extendHom_injective
    intro U hU c hc
    apply hind U hU c
    have hn := ConcreteCategory.congr_hom
      ((A.torsionSchemeYonedaIso N).hom.naturality (ConstantSectionsOn.ConstantSections.toBase U).op) (h' c)
    change (A.torsionSchemeYonedaIso N).hom.app (.op U) (ConstantSectionsOn.ConstantSections.toBase U ≫ h' c) =
      A.torsionPullback N (ConstantSectionsOn.ConstantSections.toBase U)
        ((A.torsionSchemeYonedaIso N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (h' c)) at hn
    have he : (A.torsionSchemeYonedaIso N).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest S)) (h' c) = h c :=
      ((A.torsionSchemeYonedaIso N).app (.op (ConstantSectionsOn.ConstantSections.baseTest S))).groupIsoToMulEquiv.apply_symm_apply _
    exact (congrArg (A.torsionPullback N (ConstantSectionsOn.ConstantSections.toBase U)) he).symm.trans
      (hn.symm.trans ((congrArg ((A.torsionSchemeYonedaIso N).hom.app (.op U)) hc).trans
        (map_one _)))
  exact (((A.torsionSchemeYonedaIso N).app (.op T)).groupIsoToMulEquiv.injective).comp hinj

def testToFrameBase (T : Over S) (U : Over T.left) : (Over.map T.hom).obj U ⟶ T :=
  (Over.map T.hom).map (ConstantSectionsOn.ConstantSections.toBase U) ≫ Labels.LevelCover.identityTestTo T

theorem frameAtBaseHom_natural [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (U : Over T.left) (c : Labels.LevelCover.Coefficients g N) :
    A.torsionBaseChangeEquiv T.hom U N
      ((A.pullback T.hom).torsionPullback N (ConstantSectionsOn.ConstantSections.toBase U) (UniversalFrames.LevelCover.frameAtBaseHom A T f c)) =
      Labels.LevelCover.frameTorsionHom A ((Over.map T.hom).obj U) (testToFrameBase T U ≫ f) c := by
  have hn := ConcreteCategory.congr_hom
    ((A.torsionBaseChangeIso T.hom N).hom.naturality (ConstantSectionsOn.ConstantSections.toBase U).op)
      (UniversalFrames.LevelCover.frameAtBaseHom A T f c)
  change A.torsionBaseChangeEquiv T.hom U N
      ((A.pullback T.hom).torsionPullback N (ConstantSectionsOn.ConstantSections.toBase U) (UniversalFrames.LevelCover.frameAtBaseHom A T f c)) =
    A.torsionPullback N ((Over.map T.hom).map (ConstantSectionsOn.ConstantSections.toBase U))
      (A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N (UniversalFrames.LevelCover.frameAtBaseHom A T f c)) at hn
  have hb : A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N (UniversalFrames.LevelCover.frameAtBaseHom A T f c) =
      A.torsionPullback N (Labels.LevelCover.identityTestTo T) (Labels.LevelCover.frameTorsionHom A T f c) :=
    (A.torsionBaseChangeEquiv T.hom (ConstantSectionsOn.ConstantSections.baseTest T.left) N).apply_symm_apply _
  refine hn.trans ((congrArg (A.torsionPullback N ((Over.map T.hom).map (ConstantSectionsOn.ConstantSections.toBase U))) hb).trans ?_)
  have hc : A.torsionPullback N ((Over.map T.hom).map (ConstantSectionsOn.ConstantSections.toBase U))
      (A.torsionPullback N (Labels.LevelCover.identityTestTo T) (Labels.LevelCover.frameTorsionHom A T f c)) =
      A.torsionPullback N (testToFrameBase T U) (Labels.LevelCover.frameTorsionHom A T f c) := by
    apply Subtype.ext
    exact (Category.assoc ((Over.map T.hom).map (ConstantSectionsOn.ConstantSections.toBase U)) (Labels.LevelCover.identityTestTo T)
      (Labels.LevelCover.frameTorsionHom A T f c).val).symm
  exact hc.trans (Labels.LevelCover.frameTorsionHom_natural A (testToFrameBase T U) f c)

/-- Every component of the universal frame homomorphism is injective,
including components evaluated on disconnected or nonreduced tests. -/
theorem frameLevelMap_injective [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (U : Over T.left) : Function.Injective ((UniversalFrames.LevelCover.frameLevelMap A T f).app (.op U)) := by
  apply torsionSectionExtension_injective
  intro V hV c hc
  let : Nonempty ((Over.map T.hom).obj V).left := hV
  apply frameTorsionHom_injective A ((Over.map T.hom).obj V) (testToFrameBase T V ≫ f)
  have hn := frameAtBaseHom_natural A T f V c
  exact hn.symm.trans ((congrArg (A.torsionBaseChangeEquiv T.hom V N) hc).trans
    ((map_one _).trans (map_one (Labels.LevelCover.frameTorsionHom A _ _)).symm))

end

/-! The frame construction yields an actual monomorphism of group
schemes, before any full-level isomorphism is available. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem yonedaGroupPreimage_points {B : Scheme.{0}} {X Y : Over B}
    [GrpObj X] [GrpObj Y] (α : yonedaGrpObj X ⟶ yonedaGrpObj Y)
    (U : Over B) (x : U ⟶ X) :
    α.app (.op U) x = x ≫
      (yonedaGrpFullyFaithful.preimage (X := Grp.mk X) (Y := Grp.mk Y) α).hom.hom := by
  have h := yonedaGrpFullyFaithful.map_preimage (X := Grp.mk X) (Y := Grp.mk Y) α
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h (.op U)) x).symm

variable {S : Scheme.{0}} {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def frameYonedaMap (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    yonedaGrpObj (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left) ⟶
      yonedaGrpObj ((A.pullback T.hom).torsionScheme N) :=
  (HilbertConstruction.Geometric.GeometricLevel.constantFullLevelYonedaIso g N T.left).hom ≫ UniversalFrames.LevelCover.frameLevelMap A T f ≫
    ((A.pullback T.hom).torsionSchemeYonedaIso N).inv

def frameGroupSchemeMap (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    Grp.mk (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left) ⟶
      Grp.mk ((A.pullback T.hom).torsionScheme N) :=
  yonedaGrpFullyFaithful.preimage (frameYonedaMap A T f)

def frameSchemeMap (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left ⟶ (A.pullback T.hom).torsionScheme N :=
  (frameGroupSchemeMap A T f).hom.hom

instance frameSchemeMap_isMonHom (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    IsMonHom (frameSchemeMap A T f) := (frameGroupSchemeMap A T f).hom.isMonHom_hom

theorem frameSchemeMap_points (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (U : Over T.left) (x : U ⟶ HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left) :
    (frameYonedaMap A T f).app (.op U) x = x ≫ frameSchemeMap A T f :=
  yonedaGroupPreimage_points (frameYonedaMap A T f) U x

theorem frameYonedaMap_injective [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N)
    (U : Over T.left) : Function.Injective ((frameYonedaMap A T f).app (.op U)) :=
  ((((A.pullback T.hom).torsionSchemeYonedaIso N).app (.op U)).groupIsoToMulEquiv.symm.injective).comp
    ((frameLevelMap_injective A T f U).comp
      (((HilbertConstruction.Geometric.GeometricLevel.constantFullLevelYonedaIso g N T.left).app (.op U)).groupIsoToMulEquiv.injective))

theorem frameSchemeMap_mono [NeZero N] (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    Mono (frameSchemeMap A T f) := by
  constructor
  intro U x y h
  apply frameYonedaMap_injective A T f U
  exact (frameSchemeMap_points A T f U x).trans
    (h.trans (frameSchemeMap_points A T f U y).symm)

/-- The actual universal group-scheme map is an isomorphism wherever a
full level is known, by comparison of the constructed natural maps. -/
theorem frameGroupSchemeMap_eq_split [NeZero N] (α : A.FullLevel N)
    (T : Over S) (f : T ⟶ Level.Cover.LevelCover.frameScheme A N) :
    frameGroupSchemeMap A T f =
      ((Labels.LevelCover.fullLevelFromFrame A α T f).groupSchemeIso).hom := by
  change yonedaGrpFullyFaithful.preimage
    (X := Grp.mk (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left))
    (Y := Grp.mk ((A.pullback T.hom).torsionScheme N)) (frameYonedaMap A T f) =
    yonedaGrpFullyFaithful.preimage
      (X := Grp.mk (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left))
      (Y := Grp.mk ((A.pullback T.hom).torsionScheme N))
      (HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.yonedaLevelEquiv (Labels.LevelCover.fullLevelFromFrame A α T f)).hom
  apply congrArg (fun h : yonedaGrpObj (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left) ⟶
      yonedaGrpObj ((A.pullback T.hom).torsionScheme N) =>
    yonedaGrpFullyFaithful.preimage
      (X := Grp.mk (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N T.left))
      (Y := Grp.mk ((A.pullback T.hom).torsionScheme N)) h)
  change (HilbertConstruction.Geometric.GeometricLevel.constantFullLevelYonedaIso g N T.left).hom ≫ UniversalFrames.LevelCover.frameLevelMap A T f ≫
      ((A.pullback T.hom).torsionSchemeYonedaIso N).inv = _
  rw [UniversalFrames.LevelCover.frameLevelMap_eq_split A α T f]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover
