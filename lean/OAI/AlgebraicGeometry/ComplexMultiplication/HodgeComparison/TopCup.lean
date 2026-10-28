import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers
import OAI.AlgebraicTopology.DeRham.Comparison.TopBidegree

/-! # Top Cup -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TopCup.CM.Construction

noncomputable section

section

/-! Off-diagonal pure forms vanish in real top degree. In particular,
two holomorphic one-forms paired with the penultimate Kähler power vanish. -/

open scoped _root_.Manifold ContDiff

section DegreeCast

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n m : ℕ}

theorem closedManifoldDegreeCast_injective (h : n = m) :
    Function.Injective (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h :
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M m) := by
  subst m
  exact Function.injective_id

theorem closedManifoldDegreeCast_zero (h : n = m) :
    AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h (0 : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) = 0 := by
  subst m
  rfl

end DegreeCast

theorem holomorphic_pair_kahler_power_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val.val)
    (hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 b.val.val) :
    AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a b) (Powers.CM.Construction.fubiniStudyPower V k) = 0 := by
  let c := AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a b) (Powers.CM.Construction.fubiniStudyPower V k)
  let h : (1 + 1) + (k + k) = (2 + k) + (0 + k) := by omega
  have hab := AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.hasManifoldBidegree_wedge ha hb
  have hab' : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 2 0
      (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a b).val.val := hab
  have hc := AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.hasManifoldBidegree_wedge hab' (Powers.CM.Construction.fubiniStudyPower_hasBidegree V k)
  have hz : (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h c).val = 0 :=
    Subtype.ext (Analysis.DifferentialForms.Manifold.PurePullback.pureManifoldForm_eq_zero_of_offDiagonal_top hc (by omega) (by omega))
  have hcast : AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldDegreeCast h c = 0 := Subtype.ext hz
  apply closedManifoldDegreeCast_injective h
  exact hcast.trans (closedManifoldDegreeCast_zero h).symm

end

/-! Cup two actual H¹ classes against a rational Kähler power.
The complexification agrees with the geometric product and is isotropic
on the canonical holomorphic Hodge piece. -/

def rationalH1TopCup (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    V.rationalCohomology 1 →ₗ[ℚ] V.rationalCohomology 1 →ₗ[ℚ]
      V.rationalCohomology (2 + (k + k)) :=
  (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 1 1).compr₂
    ((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 2 (k + k)).flip (Powers.CM.Construction.fubiniStudyPowerQ V k))

def complexH1TopCup (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    V.complexCohomology 1 →ₗ[ℂ] V.complexCohomology 1 →ₗ[ℂ]
      V.complexCohomology (2 + (k + k)) :=
  (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 1 1).compr₂
    ((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 2 (k + k)).flip
      (V.rationalCohomologyInclusion (k + k) (Powers.CM.Construction.fubiniStudyPowerQ V k)))

theorem rationalH1TopCup_comparison (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a b : V.rationalCohomology 1) :
    V.rationalCohomologyInclusion (2 + (k + k)) (rationalH1TopCup V k a b) =
      complexH1TopCup V k (V.rationalCohomologyInclusion 1 a) (V.rationalCohomologyInclusion 1 b) := by
  have h₁ := RationalCup.CM.Construction.rationalToComplexCohomology_cup (Betti.Scheme.schemePointSpace V.toOver) 2 (k + k)
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 1 1 a b) (Powers.CM.Construction.fubiniStudyPowerQ V k)
  have h₂ := RationalCup.CM.Construction.rationalToComplexCohomology_cup (Betti.Scheme.schemePointSpace V.toOver) 1 1 a b
  exact h₁.trans (congrArg
    (fun t : V.complexCohomology 2 => AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver)
      2 (k + k) t (V.rationalCohomologyInclusion (k + k) (Powers.CM.Construction.fubiniStudyPowerQ V k))) h₂)

theorem complexH1TopCup_holomorphic_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a b : V.complexCohomology 1) (ha : a ∈ V.pureBettiSubspace 1 0)
    (hb : b ∈ V.pureBettiSubspace 1 0) : complexH1TopCup V k a b = 0 := by
  obtain ⟨a', ha', hea⟩ := (V.mem_pureBettiSubspace_iff 1 0 a).mp ha
  obtain ⟨b', hb', heb⟩ := (V.mem_pureBettiSubspace_iff 1 0 b).mp hb
  have hz := holomorphic_pair_kahler_power_zero V k hdim a' b'
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree a'.val.val).mpr ha')
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree b'.val.val).mpr hb')
  have h₁ := AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_wedge V a' b'
  have h₂ := AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_wedge V (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a' b') (Powers.CM.Construction.fubiniStudyPower V k)
  change AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 a' = a at hea
  change AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 b' = b at heb
  have hk : AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V (k + k) (Powers.CM.Construction.fubiniStudyPower V k) =
      V.rationalCohomologyInclusion (k + k) (Powers.CM.Construction.fubiniStudyPowerQ V k) := Powers.CM.Construction.fubiniStudyPower_comparison V k
  rw [hea, heb] at h₁
  rw [h₁, hk] at h₂
  have hzero : AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V (2 + (k + k))
      (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge a' b') (Powers.CM.Construction.fubiniStudyPower V k)) = 0 := by
    rw [hz]
    unfold AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass
    rw [map_zero, map_zero]
  exact h₂.symm.trans hzero

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TopCup.CM.Construction
