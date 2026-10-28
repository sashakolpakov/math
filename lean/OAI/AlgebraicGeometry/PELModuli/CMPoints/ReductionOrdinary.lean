import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionPoint
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GeometricSectionLift
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionOrdinaryIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Reduction Ordinary -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The ordinary count on the integral CM section is the actual
geometric-fiber count at its point in the specified PEL reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

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

def Models.RankThreePELModel.CMSpreadData.IntegralComponentData.familyFiberComparison (x : R.geom a)
    (l : Spec (.of (R.fiberField a x)) ⟶ Spec (.of (AlgebraicClosure (ZMod q))))
    (hl : l ≫ T.familyPoint R jT hcop hf = R.fiberMap a x) :
    {e : (R.fiberAbelian a x).scheme ≅
      (T.polarized.abelian.pullback (l ≫ T.geometricBasePoint jT hcop)).scheme // IsMonHom e.hom} := by
  let A := (M.integral a).universal.data.polarized.abelian
  let f := (M.integralComponentInclusion a t).left
  let p := l ≫ T.geometricBasePoint jT hcop
  have hp : R.fiberMap a x ≫ R.projection a = (p ≫ T.point) ≫ f := by
    rw [← hl, Category.assoc, T.familyPoint_projection]
    simp only [p, f, Category.assoc]
  let eR := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.scheme (R.projection a) (R.fiberMap a x)
    ((p ≫ T.point) ≫ f) hp
  let e₁ := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (M.componentPolarized a t).abelian.scheme
    T.point p (p ≫ T.point) rfl
  let e₂ := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.scheme f (p ≫ T.point) ((p ≫ T.point) ≫ f) rfl
  let : IsMonHom eR.hom := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _
  let : IsMonHom e₁.hom := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _
  let : IsMonHom e₂.hom := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _
  refine ⟨eR ≪≫ e₂.symm ≪≫ e₁.symm, ?_⟩
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _
    (inferInstanceAs (IsMonHom eR.hom))
    (@CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _
      (inferInstanceAs (IsMonHom e₂.inv)) (inferInstanceAs (IsMonHom e₁.inv)))

theorem Models.RankThreePELModel.CMSpreadData.IntegralComponentData.isOrdinary_of_integral_section_counts
    (hcount : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q]
      (p : Spec (.of k) ⟶ T.base.base),
      Nat.card ((T.polarized.abelian.pullback p).torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) =
        q ^ (3 * M.s))
    (x : R.geom a) (hx : x ∈ Set.range (T.familyPoint R jT hcop hf)) : R.IsOrdinary a x := by
  obtain ⟨l, hl⟩ := GeometricSectionLift.geometricPoint_lifts_through_field_section (R.geometricFiber a)
    (T.familyPoint R jT hcop hf) (T.familyPoint_base R jT hcop hf) x hx
  let e := T.familyFiberComparison R jT hcop hf x l hl
  let : IsMonHom e.val.hom := e.property
  have hc := Nat.card_congr (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.torsionPointsIso e.val q
    (Over.mk (𝟙 (Spec (.of (R.fiberField a x)))))).toEquiv
  exact (OrdinaryFiberCount.isOrdinaryAt_iff_geometricFiber_count (R.abelian a) x).mpr
    (hc.trans (hcount (R.fiberField a x) (l ≫ T.geometricBasePoint jT hcop)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
