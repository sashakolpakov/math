import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralOrdinary
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticPadicBase
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentReduction

/-! # Reduction Point -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Reduce the actual integral CM section to a point of its specified
geometric PEL component, using the compatible arithmetic residue maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {hM : M.HasPrescribedBallPeriods}
  {a : M.Family} {t : Fin (M.componentCount a)} {C : M.CMSpreadData hM a t}
  (T : C.IntegralComponentData) {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
  (R : M.GoodIntegralReduction q j)
  (jT : Arithmetic.QadicChoice T.base.extension.carrier T.base.embedding q)
  (hcop : q.Coprime T.base.denominator)
  (hf : (jT.completion.toRingHom.comp (NumberField.FinitePlace.embedding jT.prime)).comp
      C.originalFieldEmbedding = j.completion.toRingHom.comp (NumberField.FinitePlace.embedding j.prime))

def Models.RankThreePELModel.CMSpreadData.IntegralComponentData.geometricBasePoint : Spec (.of (AlgebraicClosure (ZMod q))) ⟶ T.base.base :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).comp (ArithmeticPadicBase.arithmeticResidue T.base jT hcop)))

include hf in
theorem Models.RankThreePELModel.CMSpreadData.IntegralComponentData.geometricBasePoint_compatible :
    T.geometricBasePoint jT hcop ≫
      ArithmeticBaseMaps.arithmeticBaseMap M.arithmetic T.base C.originalFieldEmbedding
        (C.denominator_divides.trans T.denominator_divides) = R.geometricBase := by
  have hr := R.arithmeticResidue_compatible_with_reduction T.base C.originalFieldEmbedding
    (C.denominator_divides.trans T.denominator_divides) jT hcop hf
  dsimp only [Models.RankThreePELModel.CMSpreadData.IntegralComponentData.geometricBasePoint, ArithmeticBaseMaps.arithmeticBaseMap, Models.RankThreePELModel.GoodIntegralReduction.geometricBase]
  rw [← Spec.map_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  exact (RingHom.comp_assoc _ _ _).trans
    (congrArg (fun f => (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).comp f) hr)

def Models.RankThreePELModel.CMSpreadData.IntegralComponentData.componentPoint : Spec (.of (AlgebraicClosure (ZMod q))) ⟶ (R.geometricComponent a t).left :=
  pullback.lift (T.geometricBasePoint jT hcop ≫ T.point) (𝟙 _) (by
    rw [Category.assoc, T.point_base, T.geometricBasePoint_compatible R jT hcop hf, Category.id_comp])

theorem Models.RankThreePELModel.CMSpreadData.IntegralComponentData.componentPoint_base :
    T.componentPoint R jT hcop hf ≫ (R.geometricComponent a t).hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

def Models.RankThreePELModel.CMSpreadData.IntegralComponentData.familyPoint : Spec (.of (AlgebraicClosure (ZMod q))) ⟶ R.geom a :=
  T.componentPoint R jT hcop hf ≫ (R.geometricComponentInclusion a t).left

theorem Models.RankThreePELModel.CMSpreadData.IntegralComponentData.familyPoint_base : T.familyPoint R jT hcop hf ≫ (R.geometricFiber a).hom = 𝟙 _ := by
  change (_ ≫ (R.geometricComponentInclusion a t).left) ≫ _ = _
  rw [Category.assoc, (R.geometricComponentInclusion a t).w]
  exact T.componentPoint_base R jT hcop hf

theorem Models.RankThreePELModel.CMSpreadData.IntegralComponentData.familyPoint_projection :
    T.familyPoint R jT hcop hf ≫ R.projection a =
      (T.geometricBasePoint jT hcop ≫ T.point) ≫ (M.integralComponentInclusion a t).left := by
  have hi : (R.geometricComponentInclusion a t).left ≫ R.projection a =
      pullback.fst ((M.components a).S t).hom R.geometricBase ≫ (M.integralComponentInclusion a t).left :=
    AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (M.integralComponentInclusion a t) R.geometricBase
  have hp : T.componentPoint R jT hcop hf ≫ pullback.fst ((M.components a).S t).hom R.geometricBase =
      T.geometricBasePoint jT hcop ≫ T.point := pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => T.componentPoint R jT hcop hf ≫ f) hi).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ (M.integralComponentInclusion a t).left) hp)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
