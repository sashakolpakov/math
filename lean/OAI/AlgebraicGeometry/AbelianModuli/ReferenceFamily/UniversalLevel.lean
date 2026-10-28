import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SpanningBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.FrameRestriction

/-! # Universal Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalLevel.LevelCover

noncomputable section

/-! The full-frame scheme carries a constructed full level. The universal
coefficient morphism becomes an isomorphism on its spanning locus; its
pullback group structure is identified with the actual torsion kernel.
No torsion trivialization on the original base is supplied. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}} {g N : ℕ}

def levelOfPullbackGroupIso (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : S' ⟶ S)
    (e : Grp.mk ((Over.pullback u).obj (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N S)) ≅
      Grp.mk ((Over.pullback u).obj (A.torsionScheme N))) :
    (A.pullback u).FullLevel N :=
  HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.geometricEquiv.symm
    ((Level.BaseChange.GroupBaseChange.constantBaseChangeIso u).symm ≪≫ e ≪≫
      Level.BaseChange.GroupBaseChange.torsionBaseChangeIso A u N)

variable (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {K : Type} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

/-- The restricted universal coefficient map is an actual group-scheme
isomorphism, with the canonical pullback group structures. -/
def universalFrameGroupIso [NeZero N] :
    Grp.mk ((Over.pullback (Frame.Locus.LevelCover.fullFrameOpen A p (N := N)).ι).obj
      (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N (Level.Cover.LevelCover.frameScheme A N).left)) ≅
    Grp.mk ((Over.pullback (Frame.Locus.LevelCover.fullFrameOpen A p (N := N)).ι).obj
      ((A.pullback (Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N)) := by
  let u := (Frame.Locus.LevelCover.fullFrameOpen A p (N := N)).ι
  let m := (Over.pullback u).map (Frame.GroupScheme.LevelCover.frameSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _))
  let : IsIso m := SpanningBaseChange.LevelCover.universalFrame_overPullback_isIso A p
  let : IsMonHom m :=
    ((Over.pullback u).mapGrp.map (Frame.GroupScheme.LevelCover.frameGroupSchemeMap A (Level.Cover.LevelCover.frameScheme A N) (𝟙 _))).hom.isMonHom_hom
  exact Grp.mkIso' (asIso m)

/-- The constructed universal full level on the actual full-frame
scheme, transported through the canonical iterated-pullback comparison. -/
def universalFullLevel [NeZero N] :
    (A.pullback (Frame.Locus.LevelCover.fullFrameScheme A p (N := N)).hom).FullLevel N := by
  let u := (Frame.Locus.LevelCover.fullFrameOpen A p (N := N)).ι
  let e := A.pullbackCompIso (Level.Cover.LevelCover.frameScheme A N).hom u
  let : IsMonHom e.symm.hom := A.pullbackCompIso_symm_preservesGroup _ _
  exact (levelOfPullbackGroupIso (A.pullback (Level.Cover.LevelCover.frameScheme A N).hom)
    (Frame.Locus.LevelCover.fullFrameOpen A p).ι (universalFrameGroupIso A p)).transport
      (B := A.pullback (u ≫ (Level.Cover.LevelCover.frameScheme A N).hom)) e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalLevel.LevelCover
