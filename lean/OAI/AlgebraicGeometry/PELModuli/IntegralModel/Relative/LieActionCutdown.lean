import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankLocus

/-! # Lie Action Cutdown -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LieActionCutdown

noncomputable section

/-! Impose the exact arithmetic Lie ranks on an actual action ambient
over a varying abelian family, using the original restriction maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_reduced_relative_lie_action_cutdown
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left) (Z : Over M.left) [IsNoetherian Z.left]
    (ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback Z.hom)) :
    ∃ (W : Over M.left) (j : W ⟶ Z), IsReduced W.left ∧ IsImmersion j.left ∧ QuasiCompact j.left ∧
      PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj W) (A.pullback W.hom)
        (Integral.ActionScheme.restrictIntegralAction A ρZ j) ∧
      ∀ (T : Over M.left) [IsReduced T.left] (f : T ⟶ Z),
        PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.pullback T.hom)
          (Integral.ActionScheme.restrictIntegralAction A ρZ f) ↔ ∃! c : T ⟶ W, c ≫ j = f := by
  let ZR := (Over.map M.hom).obj Z
  let : IsNoetherian ZR.left := inferInstanceAs (IsNoetherian Z.left)
  obtain ⟨L, a, hL, ha, hqc, hc⟩ := Integral.LieRankLocus.exists_reduced_integral_lie_rank_locus P iotaO ZR (A.pullback Z.hom) ρZ
  let W : Over M.left := Over.mk (a.left ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk a.left rfl
  let : IsReduced W.left := hL
  have : IsImmersion j.left := ha
  have : Mono j := Over.mono_of_mono_left j
  have hclass (T : Over M.left) [IsReduced T.left] (f : T ⟶ Z) :
      PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.pullback T.hom)
        (Integral.ActionScheme.restrictIntegralAction A ρZ f) ↔ ∃! c : T ⟶ W, c ≫ j = f := by
    let TR := (Over.map M.hom).obj T
    let : IsReduced TR.left := inferInstanceAs (IsReduced T.left)
    let fR : TR ⟶ ZR := (Over.map M.hom).map f
    exact (Integral.LieRankRestriction.integralLieRanks_restrict_iff P iotaO M A ρZ f).trans
      ((hc TR fR).trans ((OverLocusClassification.over_existsUnique_lift_iff a fR).trans (OverLocusClassification.over_existsUnique_lift_iff j f).symm))
  refine ⟨W, j, hL, ha, hqc, (hclass W j).mpr ?_, hclass⟩
  refine ⟨𝟙 W, Category.id_comp j, ?_⟩
  intro c hc
  exact (cancel_mono j).mp (hc.trans (Category.id_comp j).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LieActionCutdown
