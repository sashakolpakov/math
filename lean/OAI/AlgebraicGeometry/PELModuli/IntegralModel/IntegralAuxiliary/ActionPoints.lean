import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionSpace
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedRelations

/-! # Action Points -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionPoints.IntegralAuxiliaryAction

noncomputable section

/-! Pairs of a classifying map and locally constant labels give the
actual points of the integral auxiliary relation on reduced tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X T W : Over (Spec (.of R))} {g L : ℕ}

theorem labels_comp (a : W ⟶ T) (f : T ⟶ ActionSpace.IntegralAuxiliaryAction.relation X g L) :
    ActionSpace.IntegralAuxiliaryAction.labels X g L W (a ≫ f) = (ActionSpace.IntegralAuxiliaryAction.labels X g L T f).comap ⟨a.left, a.left.continuous⟩ := by
  apply LocallyConstant.ext
  intro x
  rfl

def pair (f : T ⟶ X) (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L)) :
    T ⟶ ActionSpace.IntegralAuxiliaryAction.relation X g L :=
  prod.lift f ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of R)) _ T).symm b)

theorem pair_source (f : T ⟶ X) (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L)) :
    pair f b ≫ ActionSpace.IntegralAuxiliaryAction.source X g L = f := prod.lift_fst _ _

theorem pair_labels (f : T ⟶ X) (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut g L)) :
    ActionSpace.IntegralAuxiliaryAction.labels X g L T (pair f b) = b := by
  change AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of R)) _ T
    (prod.lift f ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of R)) _ T).symm b) ≫ prod.snd) = b
  rw [prod.lift_snd]
  exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of R)) _ T).apply_symm_apply b

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} [IsReduced X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem pair_target [IsReduced T.left] (f : T ⟶ X)
    (b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L)) :
    pair f b ≫ ActionSpace.IntegralAuxiliaryAction.target U hU = U.auxiliaryRelabelAt hU f b := by
  rw [ActionSpace.IntegralAuxiliaryAction.target_points, pair_source, pair_labels]

theorem homRelation_iff [IsReduced T.left] (f k : T ⟶ X) :
    AbelianModuli.ReferenceFamily.RepresentedRelations.homRelation (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) f k ↔
      ∃ b : LocallyConstant T.left (AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L),
        U.auxiliaryRelabelAt hU f b = k := by
  constructor
  · rintro ⟨a, ha, hk⟩
    refine ⟨ActionSpace.IntegralAuxiliaryAction.labels X (3 * s) L T a, ?_⟩
    have he := ActionSpace.IntegralAuxiliaryAction.target_points U hU T a
    rw [ha] at he
    exact he.symm.trans hk
  · rintro ⟨b, hb⟩
    exact ⟨pair f b, pair_source f b, (pair_target U hU f b).trans hb⟩

theorem homEquivalence (T : Over (Spec (.of R))) [IsReduced T.left] :
    Equivalence (AbelianModuli.ReferenceFamily.RepresentedRelations.homRelation (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) (T := T)) where
  refl f := (homRelation_iff U hU f f).mpr ⟨1, U.auxiliaryRelabelAt_one hU f⟩
  symm := by
    intro f k h
    obtain ⟨b, hb⟩ := (homRelation_iff U hU f k).mp h
    apply (homRelation_iff U hU k f).mpr
    refine ⟨b⁻¹, ?_⟩
    rw [← hb, U.auxiliaryRelabelAt_mul hU, mul_inv_cancel, U.auxiliaryRelabelAt_one hU]
  trans := by
    intro f k j hfk hkj
    obtain ⟨b, hb⟩ := (homRelation_iff U hU f k).mp hfk
    obtain ⟨c, hc⟩ := (homRelation_iff U hU k j).mp hkj
    apply (homRelation_iff U hU f j).mpr
    refine ⟨b * c, ?_⟩
    rw [← U.auxiliaryRelabelAt_mul hU, hb, hc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionPoints.IntegralAuxiliaryAction
