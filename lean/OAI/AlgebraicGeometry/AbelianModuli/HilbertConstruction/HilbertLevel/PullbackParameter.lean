import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters

/-! # Pullback Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PullbackParameter.HilbertLevelPullback

noncomputable section

/-! Pull the existing bounded group and full-level parameter back to an
actual Hilbert chart. The fiber product retains the specified Hilbert
point and its universal projective abelian family on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]

def forget : FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N ⟶
    Hilbert.ParameterScheme.hilbertParameterScheme S n P :=
  CompositeParameterPoints.compositeParameterProjection (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi)
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N) ≫
    FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi ≫
    FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupHilbertMap S n P g Pm Pi ≫
    FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n P g ≫ SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P

instance fullLevelParameter_noetherian :
    IsNoetherian (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left :=
  (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelQuasiProjectivePresentation S n P g Pm Pi N).noetherian

instance forget_locallyOfFiniteType : LocallyOfFiniteType (HilbertLevelPullback.forget S n P g Pm Pi N).left := by
  have h := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelQuasiProjectivePresentation S n P g Pm Pi N).locallyFiniteType
  let : LocallyOfFiniteType ((HilbertLevelPullback.forget S n P g Pm Pi N).left ≫ (Hilbert.ParameterScheme.hilbertParameterScheme S n P).hom) :=
    (HilbertLevelPullback.forget S n P g Pm Pi N).w.symm ▸ h
  exact locallyOfFiniteType_of_comp (HilbertLevelPullback.forget S n P g Pm Pi N).left (Hilbert.ParameterScheme.hilbertParameterScheme S n P).hom

instance forget_quasiCompact : QuasiCompact (HilbertLevelPullback.forget S n P g Pm Pi N).left := inferInstance

variable (Z : Over S) (c : Z ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n P)

def parameter : Over S := pullback c (HilbertLevelPullback.forget S n P g Pm Pi N)

def toChart : parameter S n P g Pm Pi N Z c ⟶ Z := pullback.fst c (HilbertLevelPullback.forget S n P g Pm Pi N)

def toFullLevel : parameter S n P g Pm Pi N Z c ⟶
    FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N :=
  pullback.snd c (HilbertLevelPullback.forget S n P g Pm Pi N)

theorem parameter_square :
    toChart S n P g Pm Pi N Z c ≫ c =
      toFullLevel S n P g Pm Pi N Z c ≫ HilbertLevelPullback.forget S n P g Pm Pi N :=
  pullback.condition

instance toChart_locallyOfFiniteType :
    LocallyOfFiniteType (toChart S n P g Pm Pi N Z c).left :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    ((IsPullback.of_hasPullback c (HilbertLevelPullback.forget S n P g Pm Pi N)).map (Over.forget S)).flip
    (forget_locallyOfFiniteType S n P g Pm Pi N)

instance toChart_quasiCompact : QuasiCompact (toChart S n P g Pm Pi N Z c).left :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    ((IsPullback.of_hasPullback c (HilbertLevelPullback.forget S n P g Pm Pi N)).map (Over.forget S)).flip
    (forget_quasiCompact S n P g Pm Pi N)

instance parameter_locallyNoetherian [IsLocallyNoetherian Z.left] :
    IsLocallyNoetherian (parameter S n P g Pm Pi N Z c).left :=
  LocallyOfFiniteType.isLocallyNoetherian (toChart S n P g Pm Pi N Z c).left

def family : Level.Data.AbelianSchemeWithFullLevel g N (parameter S n P g Pm Pi N Z c).left where
  abelian := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback
    (toFullLevel S n P g Pm Pi N Z c).left
  level := (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback
    (toFullLevel S n P g Pm Pi N Z c).left

def projective : Projective.ProjectivePresentations.ProjectivePresentation (family S n P g Pm Pi N Z c).abelian.scheme :=
  (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange
    (toFullLevel S n P g Pm Pi N Z c).left

def points (T : Over S) :
    (T ⟶ parameter S n P g Pm Pi N Z c) ≃
      {v : (T ⟶ Z) × (T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) //
        v.1 ≫ c = v.2 ≫ HilbertLevelPullback.forget S n P g Pm Pi N} where
  toFun a := ⟨(a ≫ toChart S n P g Pm Pi N Z c, a ≫ toFullLevel S n P g Pm Pi N Z c),
    (Category.assoc _ _ _).trans
      ((congrArg (fun h => a ≫ h) (parameter_square S n P g Pm Pi N Z c)).trans
        (Category.assoc _ _ _).symm)⟩
  invFun v := pullback.lift v.val.1 v.val.2 v.property
  left_inv a := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PullbackParameter.HilbertLevelPullback
