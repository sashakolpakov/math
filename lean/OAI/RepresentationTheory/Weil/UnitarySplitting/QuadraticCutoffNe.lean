import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticCutoffTranslations
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierPairing

/-! # Quadratic Cutoff Ne -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticCutoffNe.Construction

noncomputable section

section

/-! Compact quadratic phases as actual Bruhat test vectors. -/

open _root_.MeasureTheory _root_.Topology

variable {F : Type} [NormedField F] [IsUltrametricDist F] [ProperSpace F] {d : ℕ}
variable (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
variable (q : Local.FunctionsMetaplectic.Construction.Position F d → F) (hq : Continuous q) (hp : IsProperMap q)

def quadraticCutoffTest (r : ℝ) (hr : r ≠ 0) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  let D := q ⁻¹' Metric.closedBall 0 r
  have hD : IsClopen D := (IsUltrametricDist.isClopen_closedBall (0 : F) hr).preimage hq
  let f : LocallyConstant (Local.FunctionsMetaplectic.Construction.Position F d) ℂ :=
    ⟨fun x => ψ (q x), (LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous hq⟩
  refine ⟨D.indicator (fun x => ψ (q x)), Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem (f.indicator hD).isLocallyConstant ?_⟩
  apply HasCompactSupport.intro (hp.isCompact_preimage (isCompact_closedBall (0 : F) r))
  intro x hx
  exact Set.indicator_of_notMem hx _

theorem quadraticCutoffTest_apply (r : ℝ) (hr : r ≠ 0) (x : Local.FunctionsMetaplectic.Construction.Position F d) :
    (quadraticCutoffTest ψ hc q hq hp r hr).val x =
      (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) x := rfl

include hc hq hp in
theorem quadraticCutoffTest_nonzero (hzero : q 0 = 0) (r : ℝ) (hr : 0 < r) :
    quadraticCutoffTest ψ hc q hq hp r hr.ne' ≠ 0 := by
  intro hh
  have he := congrArg (fun f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d => f.val 0) hh
  have hz : (0 : Local.FunctionsMetaplectic.Construction.Position F d) ∈ q ⁻¹' Metric.closedBall 0 r := by simpa [hzero] using hr.le
  rw [quadraticCutoffTest_apply, Set.indicator_of_mem hz, hzero, ψ.map_zero_eq_one] at he
  exact one_ne_zero he

theorem quadraticCutoffTest_agree (s r : ℝ) (hs : s ≠ 0) (hr : r ≠ 0) (hsr : s ≤ r)
    (x : Local.FunctionsMetaplectic.Construction.Position F d) (hx : (quadraticCutoffTest ψ hc q hq hp s hs).val x ≠ 0) :
    (quadraticCutoffTest ψ hc q hq hp r hr).val x =
      (quadraticCutoffTest ψ hc q hq hp s hs).val x := by
  have hxs : x ∈ q ⁻¹' Metric.closedBall 0 s := by
    by_contra hn
    exact hx (by rw [quadraticCutoffTest_apply, Set.indicator_of_notMem hn])
  have hxr : x ∈ q ⁻¹' Metric.closedBall 0 r := Metric.closedBall_subset_closedBall hsr hxs
  rw [quadraticCutoffTest_apply, quadraticCutoffTest_apply,
    Set.indicator_of_mem hxs, Set.indicator_of_mem hxr]

end

section

/-! Fourier transforms of compact quadratic phases by completion of the
square on every frequency where the cutoff is invariant under the shift. -/

open _root_.MeasureTheory _root_.Topology

theorem quadratic_cutoff_fourier_formula
    {F : Type} [NormedField F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {d : ℕ}
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (q : Local.FunctionsMetaplectic.Construction.Position F d → F) (B : Local.FunctionsMetaplectic.Construction.Position F d → Local.FunctionsMetaplectic.Construction.Position F d → F)
    (hadd : ∀ v x, q (v + x) = q v + q x + B v x)
    (D : Set (Local.FunctionsMetaplectic.Construction.Position F d)) (y v : Local.FunctionsMetaplectic.Construction.Position F d)
    (hB : ∀ x, B v x = -Local.FunctionsMetaplectic.Construction.dot y x) (hD : ∀ x, v + x ∈ D ↔ x ∈ D) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (D.indicator (fun x => ψ (q x))) y =
      ψ (-q v) * ∫ x, D.indicator (fun x => ψ (q x)) x ∂μ := by
  classical
  have heq (x : Local.FunctionsMetaplectic.Construction.Position F d) :
      D.indicator (fun x => ψ (q x)) x * ψ (-Local.FunctionsMetaplectic.Construction.dot y x) =
        D.indicator (fun x => ψ (q x + B v x)) x := by
    by_cases hx : x ∈ D
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hB, ψ.map_add_eq_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  simp_rw [heq]
  exact QuadraticCutoffTranslations.Construction.quadratic_cutoff_complete_square μ ψ q B hadd D v hD

end

/-! Nonvanishing of large anisotropic Gaussian cutoffs. Fourier inversion
detects a nonzero coefficient on the compact Fourier support of a fixed
nonzero test vector. -/

open _root_.MeasureTheory _root_.Topology

theorem exists_large_quadratic_cutoff_integral_ne_zero
    {F : Type} [NontriviallyNormedField F] [CompleteSpace F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [IsUltrametricDist F] [CharZero F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1)
    (q : Local.FunctionsMetaplectic.Construction.Position F d → F) (hq : Continuous q) (hp : IsProperMap q) (hq0 : q 0 = 0)
    (B : Local.FunctionsMetaplectic.Construction.Position F d →L[F] Local.FunctionsMetaplectic.Construction.Position F d →L[F] F)
    (hadd : ∀ v x, q (v + x) = q v + q x + B v x)
    (A : Local.FunctionsMetaplectic.Construction.Position F d →L[F] Local.FunctionsMetaplectic.Construction.Position F d) (hA : ∀ y x, B (A y) x = -Local.FunctionsMetaplectic.Construction.dot y x)
    (c : ℝ) (hcpos : 0 < c) (hlow : ∀ x, c * ‖x‖ ^ 2 ≤ ‖q x‖) (R₀ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ R₀ ≤ r ∧
      (∫ x, (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) x
        ∂ Weak.Construction.referencePositionMeasure F d) ≠ 0 := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  let f := quadraticCutoffTest ψ hc q hq hp 1 one_ne_zero
  have hf : f ≠ 0 := quadraticCutoffTest_nonzero ψ hc q hq hp hq0 1 zero_lt_one
  let T := FourierUltra.Construction.ultraFourierLinearMap hF ψ hc hu hn (Weak.Construction.referencePositionMeasure F d)
  have hcompact : IsCompact (tsupport (T f).val) :=
    (UltraMultiplier.Construction.schwartzBruhat_ultra_iff.mp (T f).property).2
  obtain ⟨M, -, hM⟩ := (hcompact.image A.continuous).isBounded.exists_pos_norm_le
  obtain ⟨R, hR, htranslate⟩ := QuadraticCutoffTranslations.Construction.anisotropic_quadratic_cutoff_translation q hq B hadd c hcpos hlow M
  let r := max R₀ (max 1 R)
  have hr1 : 1 ≤ r := (le_max_left 1 R).trans (le_max_right _ _)
  have hrR : R ≤ r := (le_max_right 1 R).trans (le_max_right _ _)
  have hrpos : 0 < r := zero_lt_one.trans_le hr1
  let g := quadraticCutoffTest ψ hc q hq hp r hrpos.ne'
  refine ⟨r, hrpos, le_max_left _ _, ?_⟩
  intro hzero
  have hagree (x : Local.FunctionsMetaplectic.Construction.Position F d) (hx : f.val x ≠ 0) : g.val x = f.val x :=
    quadraticCutoffTest_agree ψ hc q hq hp 1 r one_ne_zero hrpos.ne' hr1 x hx
  obtain ⟨y, hyf, hyg⟩ := FourierPairing.Construction.ultra_fourier_common_support hF ψ hc hu hn f g hf hagree
  have hAy : ‖A y‖ ≤ M := hM (A y) ⟨y, subset_tsupport _ hyf, rfl⟩
  have hD (x : Local.FunctionsMetaplectic.Construction.Position F d) : A y + x ∈ q ⁻¹' Metric.closedBall 0 r ↔
      x ∈ q ⁻¹' Metric.closedBall 0 r := htranslate r hrR (A y) hAy x
  have hformula := quadratic_cutoff_fourier_formula (Weak.Construction.referencePositionMeasure F d) ψ q
    (fun v x => B v x) hadd (q ⁻¹' Metric.closedBall 0 r) y (A y) (hA y) hD
  rw [hzero, mul_zero] at hformula
  apply hyg
  change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Weak.Construction.referencePositionMeasure F d) g.val y = 0
  have hg : g.val = (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) := by
    funext x
    exact quadraticCutoffTest_apply ψ hc q hq hp r hrpos.ne' x
  rw [hg]
  exact hformula

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticCutoffNe.Construction
