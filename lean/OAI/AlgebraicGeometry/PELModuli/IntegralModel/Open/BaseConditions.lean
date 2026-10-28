import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiBasisPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiIsoTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankPullbackComposition

/-! # Base Conditions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseConditions

noncomputable section

/-! The literal Rosati and arithmetic Lie-rank predicates are detected
on open base covers. Rosati uses actual finite dual-map equations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem geometric_point_lifts_to_open_cover
    {S : Scheme.{0}} (C : S.OpenCover) {k : Type} [Field k] (p : Spec (.of k) ⟶ S) :
    ∃ i, ∃ q : Spec (.of k) ⟶ C.X i, q ≫ C.f i = p := by
  let i := C.idx (p default)
  have hr : Set.range p ⊆ Set.range (C.f i) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (default : Spec (.of k))]
    exact C.covers (p default)
  exact ⟨i, IsOpenImmersion.lift (C.f i) p hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem rosati_of_open_base_cover
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] (C : S.OpenCover)
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (h : ∀ i, AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback (C.f i)) (ρ.pullback (C.f i))) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ := by
  have hid : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback (𝟙 S)) (ρ.pullback (𝟙 S)) := by
    apply (Relative.RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ (𝟙 S)).mpr
    intro b
    apply congrArg ((Over.pullback (𝟙 S)).map)
    apply BaseGroupReflection.over_hom_ext_of_open_base_cover C
    intro i
    exact (Relative.RosatiBasisPullback.rosati_iff_relative_pulledBack_basis_equations A ρ (C.f i)).mp (h i) b
  let B : PEL.Has.PolarizedActionData E g δ N S := ⟨A, ρ⟩
  let e := PEL.Iso.PolarizedActionIso.pullbackId B
  exact RosatiIsoTransport.rosati_of_polarized_iso e.polarized (ρ.pullback (𝟙 S)) ρ
    (fun a => (e.action a).symm) hid

theorem integralLieRanks_of_open_base_cover
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (X : Over (Spec (.of R)))
    (C : X.left.OpenCover) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) X.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (h : ∀ i, PEL.Has.HasIntegralLieRanks P R iotaO (Over.mk (C.f i ≫ X.hom))
      (A.pullback (C.f i)) (ρ.pullback (C.f i))) :
    PEL.Has.HasIntegralLieRanks P R iotaO X A ρ := by
  intro k hk hclosed j p hp τ
  obtain ⟨i, q, hq⟩ := geometric_point_lifts_to_open_cover C p
  have hbase : q ≫ (C.f i ≫ X.hom) = Spec.map (CommRingCat.ofHom j) := by
    rw [← Category.assoc, hq]
    exact hp
  have hl := h i k j q hbase τ
  have hc := (LieRankPullbackComposition.hasLieRank_pullbackComp_iff A ρ (C.f i) q _ _).mpr hl
  exact hq ▸ hc

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseConditions
