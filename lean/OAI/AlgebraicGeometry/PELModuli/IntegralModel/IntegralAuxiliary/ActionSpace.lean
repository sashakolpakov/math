import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.RelativeRelabelMaps
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme

/-! # Action Space -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction

noncomputable section

/-! The integral auxiliary relation has the actual product with the
constant finite label group as its source. Its projection is finite etale,
and the constructed target classifies the relabeled universal family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R]

def relation (X : Over (Spec (.of R))) (g L : ℕ) : Over (Spec (.of R)) :=
  X ⨯ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of R)) (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L)

def source (X : Over (Spec (.of R))) (g L : ℕ) : relation X g L ⟶ X := prod.fst

theorem source_isPullback (X : Over (Spec (.of R))) (g L : ℕ) :
    IsPullback (prod.snd : relation X g L ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of R))
      (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L)).left (source X g L).left
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of R)) (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L)).hom X.hom :=
  (Over.isPullback_of_binaryFan_isLimit _
    (prodIsProd X (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of R)) (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L)))).flip

instance source_finite (X : Over (Spec (.of R))) (g L : ℕ) [NeZero L] :
    IsFinite (source X g L).left := MorphismProperty.of_isPullback (source_isPullback X g L) inferInstance

instance source_etale (X : Over (Spec (.of R))) (g L : ℕ) :
    Etale (source X g L).left := MorphismProperty.of_isPullback (source_isPullback X g L) inferInstance

instance relation_reduced (X : Over (Spec (.of R))) (g L : ℕ) [NeZero L] [IsReduced X.left] :
    IsReduced (relation X g L).left := Finite.EtaleReduced.finite_etale_isReduced (source X g L).left

def labels (X : Over (Spec (.of R))) (g L : ℕ) (T : Over (Spec (.of R)))
    (f : T ⟶ relation X g L) : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L) :=
  AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of R)) _ T (f ≫ prod.snd)

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

def target : relation X (3 * s) L ⟶ X :=
  U.auxiliaryRelabelAt hU (source X (3 * s) L) (labels X (3 * s) L _ (𝟙 _))

theorem target_points (T : Over (Spec (.of R))) [IsReduced T.left]
    (f : T ⟶ relation X (3 * s) L) :
    f ≫ target U hU = U.auxiliaryRelabelAt hU (f ≫ source X (3 * s) L) (labels X (3 * s) L T f) :=
  U.auxiliaryRelabelAt_natural hU f (source X (3 * s) L) (labels X (3 * s) L _ (𝟙 _))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction
