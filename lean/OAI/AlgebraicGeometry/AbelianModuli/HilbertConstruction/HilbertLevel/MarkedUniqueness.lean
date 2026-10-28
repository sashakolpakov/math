import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.ProjectiveRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.UniversalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelUniversalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterPullbackCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.FamilyGroupUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSectionExt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DataEmbeddingRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.UnitUniqueness

/-! # Marked Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.MarkedUniqueness.HilbertLevelPullback

noncomputable section

/-! The original Hilbert point and the actual marked projective sections
uniquely determine a point of the full-level Hilbert parameter over a
locally Noetherian test scheme. The zero label determines the unit, the
projective group-uniqueness theorem determines the group operations, and
all constant labels determine the original full level. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
universe u

private theorem precompose_triangle {C : Type*} [Category* C] {U X Y Z : C}
    (a : U ⟶ X) (b : X ⟶ Y) (j : Y ⟶ Z) (i : X ⟶ Z)
    (h : b ≫ j = i) : (a ≫ b) ≫ j = a ≫ i :=
  (Category.assoc _ _ _).trans (congrArg (fun k => a ≫ k) h)

private theorem precompose_triangle_left {S : Scheme.{u}} {U X Y Z : Over S}
    (a : U ⟶ X) (b : X ⟶ Y) (j : Y ⟶ Z) (i : X ⟶ Z)
    (h : b ≫ j = i) : ((a ≫ b) ≫ j).left = (a ≫ i).left :=
  congrArg Over.Hom.left (precompose_triangle a b j i h)

private theorem unit_triangle {C : Type*} [Category* C] {U X Y Z : C}
    (u : U ⟶ X) (v : U ⟶ Y) (e : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z)
    (hu : u ≫ e = v) (he : e ≫ i = j) : v ≫ i = u ≫ j :=
  (congrArg (fun k => k ≫ i) hu.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (fun k => u ≫ k) he))

private theorem unit_triangle_left {S : Scheme.{u}} {U X Y Z : Over S}
    (u : U ⟶ X) (v : U ⟶ Y) (e : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z)
    (hu : u ≫ e = v) (he : e ≫ i = j) : (v ≫ i).left = (u ≫ j).left :=
  congrArg Over.Hom.left (unit_triangle u v e i j hu he)

private theorem abelianIsoUnit_left {S : Scheme.{u}} {g : ℕ}
    {A B : Abelian.Schemes.AbelianScheme g S} (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    η[A.scheme].left ≫ e.hom.left = η[B.scheme].left :=
  congrArg Over.Hom.left (IsMonHom.one_hom e.hom)

section MarkedTransport
variable {S : Scheme.{u}} {g N n : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

private theorem levelSection_transport (l : A.FullLevel N) (k : B.FullLevel N)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (hl : l.transport e = k)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    B.fullLevelGlobalSection k c = A.fullLevelGlobalSection l c ≫ e.hom.left :=
  (congrArg (fun q => B.fullLevelGlobalSection q c) hl.symm).trans
    (Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport l e c)

private theorem embeddedLevel_one (l : A.FullLevel N)
    (j : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) :
    (l.hom.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S 1)).val ≫ j =
      η[A.scheme] ≫ j := by
  apply Over.OverMorphism.ext
  exact congrArg (fun z => z ≫ j.left) (Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_one l)
end MarkedTransport

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ)

local instance markedRecoveryUniversalGroup :
    GrpObj (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi

private theorem groupPointFamilyIso_embedding {T : Over S}
    (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    (Fixed.GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi y).hom ≫
      ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).projective S n P g Pm Pi).embedding =
      ((FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding :=
  Fixed.DataEmbeddingRecovery.fixedDimensionHilbertGroupPointFamilyIso_embedding S n P g Pm Pi y

private theorem abelianPointFamilyIso_embedding {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (Fixed.UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi y).hom ≫
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T y).val.projective
        S n P g Pm Pi).embedding =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding :=
  Fixed.DataEmbeddingRecovery.fixedDimensionHilbertAbelianPointFamilyIso_embedding S n P g Pm Pi y

private def nativeUnitMark {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    Over.mk (𝟙 T.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n :=
  D.embeddedUnit S n P g Pm Pi

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem nativeAbelianUnit_left {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    η[(D.abelianScheme S n P g Pm Pi).scheme].left = D.val.2.val.val.unit.left := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem nativeUnitMark_left {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    (nativeUnitMark S n P g Pm Pi D).left =
      D.val.2.val.val.unit.left ≫ (D.val.projective S n P g Pm Pi).embedding.left := rfl

private theorem nativeUnitTransport_left {T : Over S}
    (a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    η[((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).scheme].left ≫
      (Fixed.UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi a).hom.left =
      (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T a).val.2.val.val.unit.left :=
  (abelianIsoUnit_left (Fixed.UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi a)).trans
    (nativeAbelianUnit_left S n P g Pm Pi
      (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T a))

private theorem abelianPointFamilyIso_embedding_left {T : Over S}
    (a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (Fixed.UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi a).hom.left ≫
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T a).val.projective
        S n P g Pm Pi).embedding.left =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange a.left).embedding.left :=
  congrArg Over.Hom.left (abelianPointFamilyIso_embedding S n P g Pm Pi a)

private theorem nativeUnitMark_recovery_left {T : Over S}
    (a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (nativeUnitMark S n P g Pm Pi
      (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T a)).left =
      η[((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).scheme].left ≫
        ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange a.left).embedding.left :=
  (nativeUnitMark_left S n P g Pm Pi
    (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T a)).trans
      (unit_triangle _ _ _ _ _ (nativeUnitTransport_left S n P g Pm Pi a)
        (abelianPointFamilyIso_embedding_left S n P g Pm Pi a))

private theorem nativeUnitMark_recovery {T : Over S}
    (a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    nativeUnitMark S n P g Pm Pi (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T a) =
      η[((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).scheme] ≫
        ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange a.left).embedding := by
  apply Over.OverMorphism.ext
  exact nativeUnitMark_recovery_left S n P g Pm Pi a

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The same fixed Hilbert point and embedded unit force equality of the
actual bounded group operations and hence of the native abelian data. -/
private theorem nativeAbelianData_eq_of_unitMark {T : Over S} [IsLocallyNoetherian T.left]
    (D E : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T)
    (hc : D.val.1 = E.val.1)
    (hu : nativeUnitMark S n P g Pm Pi D = nativeUnitMark S n P g Pm Pi E) : D = E :=
  FixedDimension.PointData.FixedDimensionHilbertAbelianData.eq_of_hilbert_eq_embeddedUnit S n P g Pm Pi D E hc hu

variable (N : ℕ) [NeZero N]

/-- The actual full-level sections in the existing universal projective
presentation, pulled back to the given test scheme. -/
def markedPoint {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    Over.mk (𝟙 T.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n :=
  (((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback y.left).hom.app
    (.op (Over.mk (𝟙 T.left))) (LocallyConstant.const T.left c)).val ≫
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding

/-- These are precisely the same sections in the native pullback of the
original Hilbert family, composed with its original projective inclusion. -/
theorem markedPoint_nativeHilbert {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion, inferInstance⟩
    ((((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback y.left).hom.app
      (.op (Over.mk (𝟙 T.left))) (LocallyConstant.const T.left c)).val ≫
      (ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso S n P g Pm Pi N y.left).hom) ≫
      (Q.baseChange (y.left ≫ (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left)).embedding =
        markedPoint S n P g Pm Pi N y c := by
  apply Over.OverMorphism.ext
  exact precompose_triangle_left _ _ _ _ (ProjectiveRecovery.HilbertLevelPullback.universalFamilyPullbackIso_embedding S n P g Pm Pi N y.left)

private def abelianLevelMark {T : Over S}
    (D : Σ a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).FullLevel N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    Over.mk (𝟙 T.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n :=
  (D.2.hom.app (.op (Over.mk (𝟙 T.left))) (LocallyConstant.const T.left c)).val ≫
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding

private theorem fullLevelPointFamilyIso_embedding {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (Fixed.LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y).hom ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).embedding =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding :=
  Fixed.DataEmbeddingRecovery.fixedDimensionHilbertFullLevelPointFamilyIso_embedding S n P g Pm Pi N y

private theorem fullLevelPointFamilyIso_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (Fixed.LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y).hom.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).embedding.left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding.left :=
  congrArg Over.Hom.left (fullLevelPointFamilyIso_embedding S n P g Pm Pi N y)

private theorem markedPoint_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    (markedPoint S n P g Pm Pi N y c).left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback y.left).fullLevelGlobalSection
        ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback y.left) c ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding.left := rfl

omit [NeZero N] in
private theorem abelianLevelMark_left {T : Over S}
    (D : Σ a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).FullLevel N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    (abelianLevelMark S n P g Pm Pi N D c).left =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback D.1.left).fullLevelGlobalSection D.2 c ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding.left := rfl

private theorem fullLevelPoint_globalSection {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).fullLevelGlobalSection
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).2 c =
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback y.left).fullLevelGlobalSection
      ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback y.left) c ≫
      (Fixed.LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y).hom.left :=
  levelSection_transport
    ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback y.left)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).2
    (Fixed.LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y)
    (Fixed.LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso_level S n P g Pm Pi N y) c

private theorem abelianLevelMark_recovery_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    (abelianLevelMark S n P g Pm Pi N
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y) c).left =
        (markedPoint S n P g Pm Pi N y c).left :=
  (abelianLevelMark_left S n P g Pm Pi N
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y) c).trans
      ((unit_triangle _ _ _ _ _ (fullLevelPoint_globalSection S n P g Pm Pi N y c).symm
        (fullLevelPointFamilyIso_embedding_left S n P g Pm Pi N y)).trans
          (markedPoint_left S n P g Pm Pi N y c).symm)

private theorem abelianLevelMark_recovery {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    abelianLevelMark S n P g Pm Pi N
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y) c =
        markedPoint S n P g Pm Pi N y c := by
  apply Over.OverMorphism.ext
  exact abelianLevelMark_recovery_left S n P g Pm Pi N y c

omit [NeZero N] in
private theorem abelianLevelMark_one_left {T : Over S}
    (D : Σ a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).FullLevel N) :
    (abelianLevelMark S n P g Pm Pi N D 1).left =
      η[((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback D.1.left).scheme].left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding.left :=
  (abelianLevelMark_left S n P g Pm Pi N D 1).trans
    (congrArg (fun a => a ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding.left)
      (Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_one D.2))

private theorem nativeUnitMark_fullLevelPoint_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (nativeUnitMark S n P g Pm Pi
      (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1)).left =
      (markedPoint S n P g Pm Pi N y 1).left :=
  (nativeUnitMark_recovery_left S n P g Pm Pi
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1).trans
      ((abelianLevelMark_one_left S n P g Pm Pi N
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y)).symm.trans
          (abelianLevelMark_recovery_left S n P g Pm Pi N y 1))

private theorem nativeUnitMark_fullLevelPoint {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    nativeUnitMark S n P g Pm Pi
      (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1) =
      markedPoint S n P g Pm Pi N y 1 := by
  apply Over.OverMorphism.ext
  exact nativeUnitMark_fullLevelPoint_left S n P g Pm Pi N y

private theorem fullLevelPoint_hilbert {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1).val.1 ≫
      FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n P g ≫ SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P =
        y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N := by
  change (((y ≫ CompositeParameterPoints.compositeParameterProjection
    (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N)) ≫
      FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi) ≫
        FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupHilbertMap S n P g Pm Pi) ≫
      FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n P g ≫ SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P = _
  simp only [PullbackParameter.HilbertLevelPullback.forget, Category.assoc]
  exact Category.assoc _ _ _

omit [NeZero N] in
private theorem abelianLevelData_eq_of_marks {T : Over S}
    (D E : Σ a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).FullLevel N)
    (ha : D.1 = E.1)
    (hm : ∀ c, abelianLevelMark S n P g Pm Pi N D c = abelianLevelMark S n P g Pm Pi N E c) :
    D = E := by
  rcases D with ⟨a, l⟩
  rcases E with ⟨b, k⟩
  change a = b at ha
  cases ha
  let : IsClosedImmersion
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange a.left).embedding.left :=
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange a.left).closedImmersion
  have hl : l = k := by
    apply Abelian.Schemes.AbelianScheme.FullLevel.ext_globalSections
    intro c
    apply (cancel_mono
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange a.left).embedding.left).mp
    exact congrArg Over.Hom.left (hm c)
  exact congrArg (fun j => (⟨a, j⟩ : Σ a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi,
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback a.left).FullLevel N)) hl

/-- Over a locally Noetherian test scheme, the original Hilbert point and
all actual embedded full-level sections determine the parameter point. -/
theorem points_eq_of_hilbert_eq_markedPoints {T : Over S} [IsLocallyNoetherian T.left]
    (y z : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (hH : y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = z ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N)
    (hm : ∀ c, markedPoint S n P g Pm Pi N y c = markedPoint S n P g Pm Pi N z c) :
    y = z := by
  let E := FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T
  let F := FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T
  let a := (E y).1
  let b := (E z).1
  have hc : (F a).val.1 = (F b).val.1 := by
    let : IsOpenImmersion (SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P).left :=
      Open.ParameterPoints.openParameterInclusion_open (Hilbert.ParameterScheme.hilbertParameterScheme S n P) (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).smoothBaseOpen
    let : Mono (FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n P g) := Over.mono_of_mono_left _
    let : Mono (SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P) := Over.mono_of_mono_left _
    apply (cancel_mono (FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n P g)).mp
    apply (cancel_mono (SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P)).mp
    simpa only [Category.assoc] using
      (fullLevelPoint_hilbert S n P g Pm Pi N y).trans
        (hH.trans (fullLevelPoint_hilbert S n P g Pm Pi N z).symm)
  have hu : nativeUnitMark S n P g Pm Pi (F a) = nativeUnitMark S n P g Pm Pi (F b) :=
    (nativeUnitMark_fullLevelPoint S n P g Pm Pi N y).trans
      ((hm 1).trans (nativeUnitMark_fullLevelPoint S n P g Pm Pi N z).symm)
  have hab : a = b := F.injective (nativeAbelianData_eq_of_unitMark S n P g Pm Pi (F a) (F b) hc hu)
  apply E.injective
  apply abelianLevelData_eq_of_marks S n P g Pm Pi N (E y) (E z) hab
  intro c
  exact (abelianLevelMark_recovery S n P g Pm Pi N y c).trans
    ((hm c).trans (abelianLevelMark_recovery S n P g Pm Pi N z c).symm)

/-- Scheme-morphism form, directly applicable to equations on the actual
projective marked sections used in the parameter construction. -/
theorem points_eq_of_hilbert_eq_projectiveSections {T : Over S} [IsLocallyNoetherian T.left]
    (y z : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)
    (hH : y ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N = z ≫ PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N)
    (hm : ∀ c : Multiplicative (Fin (2 * g) → ZMod N),
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback y.left).fullLevelGlobalSection
        ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback y.left) c ≫
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding.left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback z.left).fullLevelGlobalSection
        ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback z.left) c ≫
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange z.left).embedding.left) :
    y = z := by
  apply points_eq_of_hilbert_eq_markedPoints S n P g Pm Pi N y z hH
  intro c
  exact Over.OverMorphism.ext (hm c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.MarkedUniqueness.HilbertLevelPullback
