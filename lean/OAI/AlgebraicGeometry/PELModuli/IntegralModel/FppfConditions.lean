import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseConditions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeGeometricPointLift
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionDescent

/-! # Fppf Conditions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfConditions

noncomputable section

/-! The literal Rosati and arithmetic Lie-rank conditions descend
through actual faithfully flat or surjective finite-type base covers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem rosati_of_fppf_baseChange
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S T : Scheme.{0}} [IsReduced S] [IsNoetherian S]
    (u : T ⟶ S) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (h : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback u) (ρ.pullback u)) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ := by
  have hid : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback (𝟙 S)) (ρ.pullback (𝟙 S)) := by
    apply (Relative.RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ (𝟙 S)).mpr
    intro b
    apply congrArg ((Over.pullback (𝟙 S)).map)
    apply (Over.pullback u).map_injective
    exact (Relative.RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ u).mp h b
  let B : PEL.Has.PolarizedActionData E g δ N S := ⟨A, ρ⟩
  let e := PEL.Iso.PolarizedActionIso.pullbackId B
  exact RosatiIsoTransport.rosati_of_polarized_iso e.polarized (ρ.pullback (𝟙 S)) ρ
    (fun a => (e.action a).symm) hid

theorem integralLieRanks_of_surjective_baseChange
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) {X Y : Over (Spec (.of R))}
    (u : Y ⟶ X) [Surjective u.left] [LocallyOfFiniteType u.left]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) X.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (h : PEL.Has.HasIntegralLieRanks P R iotaO Y (A.pullback u.left) (ρ.pullback u.left)) :
    PEL.Has.HasIntegralLieRanks P R iotaO X A ρ := by
  intro k hk hclosed j p hp τ
  obtain ⟨q, hq⟩ := Finite.TypeGeometricPointLift.exists_geometric_point_lift u.left p
  have hbase : q ≫ Y.hom = Spec.map (CommRingCat.ofHom j) := by
    rw [← u.w, ← Category.assoc, hq]
    exact hp
  have hl := h k j q hbase τ
  have hc := (LieRankPullbackComposition.hasLieRank_pullbackComp_iff A ρ u.left q _ _).mpr hl
  exact hq ▸ hc

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfConditions
