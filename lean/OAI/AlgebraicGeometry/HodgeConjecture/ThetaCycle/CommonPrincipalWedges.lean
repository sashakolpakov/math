import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSourceFamilies
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RefinementForms
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.WedgeFormClasses

/-! # Common Principal Wedges -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CommonPrincipalWedges.CM

noncomputable section

/-! Put every factor of two finite source-wedge decompositions on one
actual principal cover. Full HeckeCycles controls all four sign families there,
and the covering degree preserves the nonzero two-form product. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def HasCMWedgeProduct (S : Cm.ProjectiveSurface) : Prop :=
  ∃ ξ ζ : S.variety.complexCohomology 2,
    ξ ∈ Cm.wedgeSpan S.variety
      (Cm.cmLineSpan K S.variety (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 S.variety) (v 0) 1)
      (Cm.cmLineSpan K S.variety (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 S.variety) (v 1) 1) ∧
    ζ ∈ Cm.wedgeSpan S.variety
      (Cm.cmLineSpan K S.variety (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 S.variety) (v 2) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K))
      (Cm.cmLineSpan K S.variety (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 S.variety) (v 3) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) ∧
    S.evaluate (Cm.cup S.variety 2 2 ξ ζ) ≠ 0

include hid in
theorem common_principal_wedge_product (hHeckeCycles : HeckeCycles.CM.HeckeCyclesInput)
    (N : ℕ) (hN : 0 < N) (hDN : D.depth ∣ N)
    (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (D.surface N hN hDN).surface.variety.analyticModel
      (D.surface N hN hDN).surface.variety.analyticSpace 2)
    (r s : ℕ) (φ₀ ψ₀ : Fin r → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places))
    (φ₁ ψ₁ : Fin s → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places)) (c₀ c₁ : ℂ)
    (hα : CoverPullback.CM.ballCoverPullback K D.ball N (D.surface N hN hDN).surface.variety
      (D.surface N hN hDN).projection (D.surface N hN hDN).isBallCover 2 α.val =
        ∑ i, c₀ • BallForms.CM.sourceBallTwoForm K (D.initialPeriods 0) (D.initialPeriods 1) (φ₀ i) (ψ₀ i))
    (hβ : CoverPullback.CM.ballCoverPullback K D.ball N (D.surface N hN hDN).surface.variety
      (D.surface N hN hDN).projection (D.surface N hN hDN).isBallCover 2 β.val =
        ∑ i, c₁ • BallForms.CM.sourceBallTwoForm K (A.periods 0) (A.periods 1) (φ₁ i) (ψ₁ i))
    (hn : (D.surface N hN hDN).surface.evaluate
      (Cm.cup (D.surface N hN hDN).surface.variety 2 2
        (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass (D.surface N hN hDN).surface.variety 2 α)
        (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass (D.surface N hN hDN).surface.variety 2
          (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β))) ≠ 0) :
    ∃ (M : ℕ) (hM : 0 < M) (hDM : D.depth ∣ M),
      HasCMWedgeProduct K (v := v) (D.surface M hM hDM).surface := by
  let J := (Fin r ⊕ Fin r) ⊕ (Fin s ⊕ Fin s)
  let σ : J → Fin 2 ⊕ Fin 2 :=
    Sum.elim (Sum.elim (fun _ => .inl 0) (fun _ => .inl 1))
      (Sum.elim (fun _ => .inr 0) (fun _ => .inr 1))
  let Φ : J → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places) :=
    Sum.elim (Sum.elim φ₀ ψ₀) (Sum.elim φ₁ ψ₁)
  obtain ⟨L, hL, hDL, hforms⟩ := ConcreteSourceFamilies.CM.exists_actual_principal_source_classes K D A hid σ Φ hHeckeCycles
  let M := N * L
  have hM : 0 < M := Nat.mul_pos hN (lt_of_lt_of_le (by decide : 0 < 3) hL)
  have hNM : N ∣ M := dvd_mul_right _ _
  have hLM : L ∣ M := dvd_mul_left _ _
  have hDM : D.depth ∣ M := hDN.trans hNM
  let S := D.surface N hN hDN
  let T := D.surface M hM hDM
  obtain ⟨p⟩ := PeriodTotal.CM.setup_principal_refinement K D N M hN hM hDN hDM hNM
  have hs := hforms M hM hLM
  choose ω hω hωid hωc using hs
  let a₀ : Fin r → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms T.surface.variety.analyticModel T.surface.variety.analyticSpace 1 :=
    fun i => (ω (.inl (.inl i))).val
  let b₀ : Fin r → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms T.surface.variety.analyticModel T.surface.variety.analyticSpace 1 :=
    fun i => (ω (.inl (.inr i))).val
  let a₁ : Fin s → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms T.surface.variety.analyticModel T.surface.variety.analyticSpace 1 :=
    fun i => (ω (.inr (.inl i))).val
  let b₁ : Fin s → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms T.surface.variety.analyticModel T.surface.variety.analyticSpace 1 :=
    fun i => (ω (.inr (.inr i))).val
  have heα : RefinementForms.CM.projectiveClosedPullback p.map 2 α = ∑ i, c₀ • AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a₀ i) (b₀ i) := by
    apply WedgeFormClasses.CM.closed_form_eq_sum_source_wedges K (D.initialPeriods 0) (D.initialPeriods 1)
      M T.surface.variety T.projection T.isBallCover a₀ b₀ φ₀ ψ₀ (fun _ => c₀)
      (fun i => hω (.inl (.inl i))) (fun i => hω (.inl (.inr i)))
    exact (RefinementForms.CM.refinement_ball_form_pullback K p 2 α).trans hα
  have heβ : RefinementForms.CM.projectiveClosedPullback p.map 2 β = ∑ i, c₁ • AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a₁ i) (b₁ i) := by
    apply WedgeFormClasses.CM.closed_form_eq_sum_source_wedges K (A.periods 0) (A.periods 1)
      M T.surface.variety T.projection T.isBallCover a₁ b₁ φ₁ ψ₁ (fun _ => c₁)
      (fun i => hω (.inr (.inl i))) (fun i => hω (.inr (.inr i)))
    exact (RefinementForms.CM.refinement_ball_form_pullback K p 2 β).trans hβ
  refine ⟨M, hM, hDM, AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass T.surface.variety 2 (RefinementForms.CM.projectiveClosedPullback p.map 2 α),
    AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass T.surface.variety 2 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm
      (RefinementForms.CM.projectiveClosedPullback p.map 2 β)), ?_, ?_, RefinementForms.CM.refinement_form_cup_nonzero K p α β hn⟩
  · rw [heα]
    exact WedgeFormClasses.CM.closed_wedge_sum_class_mem T.surface.variety _ _ a₀ b₀ (fun _ => c₀)
      (fun i => hωid (.inl (.inl i))) (fun i => hωid (.inl (.inr i)))
  · rw [heβ]
    exact WedgeFormClasses.CM.conjugate_closed_wedge_sum_class_mem T.surface.variety _ _ a₁ b₁ (fun _ => c₁)
      (fun i => hωc (.inr (.inl i))) (fun i => hωc (.inr (.inr i)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CommonPrincipalWedges.CM
