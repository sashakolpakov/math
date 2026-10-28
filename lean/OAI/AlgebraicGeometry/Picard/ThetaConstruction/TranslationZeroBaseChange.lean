import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineTranslation
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceZeroScheme
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Translation Zero Base Change -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric

noncomputable section

/-! The actual represented translation zero scheme commutes with
base change. Its comparison is constructed from the original all-test
factorization properties and retains the inclusion into the abelian
family; either actual projective presentation may be used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

variable {S S' : Scheme} [IsLocallyNoetherian S] [IsLocallyNoetherian S']
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : S' ⟶ S)
    (P' : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (A.pullback f).scheme)

local instance translationZeroBaseChange_sourceNoetherian : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
local instance translationZeroBaseChange_targetNoetherian : IsLocallyNoetherian (A.pullback f).scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian (A.pullback f).scheme.hom

omit [IsLocallyNoetherian S'] in
theorem translationZero_baseChange_factorization (U : Over S') (a : U ⟶ (A.pullback f).scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f)
      (L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f))).relativeValue a =
        AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass (A.pullback f).scheme U ↔
      ∃ x : U ⟶ (Over.pullback f).obj (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P),
        x ≫ (Over.pullback f).map (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) = a := by
  rw [ReferenceLineTranslation.Geometric.relativeDifference_zero_baseChange_iff, RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization]
  let Z := RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P
  let i := RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P
  let adj := Over.mapPullbackAdj f
  have hn (x : U ⟶ (Over.pullback f).obj Z) :
      A.baseChangePointsEquiv f U (x ≫ (Over.pullback f).map i) =
        (adj.homEquiv U Z).symm x ≫ i := adj.homEquiv_naturality_right_symm x i
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨adj.homEquiv U Z x, ?_⟩
    apply (A.baseChangePointsEquiv f U).injective
    exact (hn _).trans ((congrArg (fun z => z ≫ i) ((adj.homEquiv U Z).symm_apply_apply x)).trans hx)
  · rintro ⟨x, hx⟩
    exact ⟨(adj.homEquiv U Z).symm x,
      (hn x).symm.trans (congrArg (A.baseChangePointsEquiv f U) hx)⟩

theorem exists_translationZero_baseChange_iso :
    ∃ e : (Over.pullback f).obj (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P) ≅
        RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback f)
          (L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)) P',
      e.hom ≫ RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion (A.pullback f)
        (L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)) P' =
          (Over.pullback f).map (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) := by
  let L' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.pullback f).scheme.left := L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)
  let Z := (Over.pullback f).obj (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily A L P)
  let Z' := RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroFamily (A.pullback f) L' P'
  let i : Z ⟶ (A.pullback f).scheme := (Over.pullback f).map (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P)
  let j : Z' ⟶ (A.pullback f).scheme := RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion (A.pullback f) L' P'
  let : Mono (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) :=
    RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  let : Mono i := (Over.pullback f).map_mono (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P)
  let : Mono j := RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P' (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f) L')
  have hi : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f) L').relativeValue i =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass (A.pullback f).scheme Z :=
    (translationZero_baseChange_factorization A L P f Z i).mpr ⟨𝟙 Z, Category.id_comp i⟩
  obtain ⟨u, hu⟩ := (RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization (A.pullback f) L' P' Z i).mp hi
  have hj : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f) L').relativeValue j =
      AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass (A.pullback f).scheme Z' :=
    RelativeZeroGroup.Geometric.RelativeRigidifiedCharts.zeroInclusion_relative_zero (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f) L') P'
  obtain ⟨v, hv⟩ := (translationZero_baseChange_factorization A L P f Z' j).mp hj
  let e : Z ≅ Z' := {
    hom := u
    inv := v
    hom_inv_id := by
      apply (cancel_mono i).mp
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun t => u ≫ t) hv).trans (hu.trans (Category.id_comp i).symm))
    inv_hom_id := by
      apply (cancel_mono j).mp
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun t => v ≫ t) hu).trans (hv.trans (Category.id_comp j).symm)) }
  exact ⟨e, hu⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationZeroBaseChange.Geometric
