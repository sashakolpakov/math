import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LieRankLocus

/-! # Lie Action Cutdown -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.LieActionCutdown

noncomputable section

/-! Impose the exact arithmetic Lie ranks on an actual action ambient
over a varying abelian family, using the original restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction

theorem exists_relative_lie_action_cutdown
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left) (Z : Over M.left) [IsNoetherian Z.left]
    (ρZ : ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback Z.hom)) :
    ∃ (W : Over M.left) (j : W ⟶ Z), IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj W) (A.pullback W.hom)
        (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A ρZ j) ∧
      ∀ (T : Over M.left) (f : T ⟶ Z),
        PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.pullback T.hom)
          (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A ρZ f) ↔ ∃! c : T ⟶ W, c ≫ j = f := by
  let ZR := (Over.map M.hom).obj Z
  let : IsNoetherian ZR.left := inferInstanceAs (IsNoetherian Z.left)
  obtain ⟨L, a, ha, hclosed, hc⟩ := Integral.LieRankLocus.exists_integral_lie_rank_locus P iotaO ZR (A.pullback Z.hom) ρZ
  let W : Over M.left := Over.mk (a.left ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk a.left rfl
  have : IsOpenImmersion j.left := ha
  have : Mono j := Over.mono_of_mono_left j
  have hclass (T : Over M.left) (f : T ⟶ Z) :
      PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.pullback T.hom)
        (PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A ρZ f) ↔ ∃! c : T ⟶ W, c ≫ j = f := by
    let TR := (Over.map M.hom).obj T
    let fR : TR ⟶ ZR := (Over.map M.hom).map f
    exact (PELModuli.IntegralModel.Integral.LieRankRestriction.integralLieRanks_restrict_iff P iotaO M A ρZ f).trans
      ((hc TR fR).trans ((PELModuli.IntegralModel.OverLocusClassification.over_existsUnique_lift_iff a fR).trans (PELModuli.IntegralModel.OverLocusClassification.over_existsUnique_lift_iff j f).symm))
  refine ⟨W, j, ha, hclosed, (hclass W j).mpr ?_, hclass⟩
  refine ⟨𝟙 W, Category.id_comp j, ?_⟩
  intro c hc
  exact (cancel_mono j).mp (hc.trans (Category.id_comp j).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.LieActionCutdown
