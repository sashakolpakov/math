import OAI.AlgebraicGeometry.Comparison.Betti.ContractionCauchyPrimitive
import OAI.AlgebraicGeometry.Comparison.Betti.Open.DolbeaultCorrection

/-! # Higher Form Coefficient Elimination -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HigherFormCoefficientElimination.Dolbeault

noncomputable section

/-! One-coordinate elimination for actual closed pure forms of degree
at least two, preserving all previously zero parameter contractions. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P]

omit [NormedSpace ℝ P] [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] in
theorem productOpen_mono {S : Opens P} {U W : Opens ℂ} (h : W ≤ U) :
    ContractionCauchyPrimitive.Dolbeault.productOpen S W ≤ ContractionCauchyPrimitive.Dolbeault.productOpen S U := fun _ hx => ⟨hx.1, h hx.2⟩

theorem exists_higherForm_coefficient_elimination {S : Opens P} {U : Opens ℂ}
    (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S U) (n + 2))
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) {x : ℂ} (hx : x ∈ U) :
    ∃ W : Opens ℂ, x ∈ W ∧ ∃ h : W ≤ U,
      ∃ u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S W) (n + 1), DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q u ∧
        let b := Open.DolbeaultCorrection.correctOpenDolbeaultForm (n + 1) (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (productOpen_mono h) a) u
        DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) b = 0 ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) b ∧
          Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S W) (n + 1) (0, 1) b = 0 ∧
          (∀ v : P, Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S U) (n + 1) (v, 0) a = 0 →
            Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S W) (n + 1) (v, 0) b = 0) := by
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (U.isOpen.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := R / 2, rOut := R, rIn_pos := half_pos hR, rIn_lt_rOut := half_lt_self hR }
  have hsupp : tsupport χ ⊆ (U : Set ℂ) := by rwa [χ.tsupport_eq]
  let W : Opens ℂ := ⟨ball x (R / 2), isOpen_ball⟩
  have hWU : W ≤ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hR.le))).trans hsub
  let h := productOpen_mono (S := S) hWU
  let ar := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h a
  let G := ContractionCauchyPrimitive.Dolbeault.contractionCauchyPrimitive (n + 1) χ a
  have hG : ContDiffOn ℝ ∞ G (ContractionCauchyPrimitive.Dolbeault.productOpen S W : Set (P × ℂ)) :=
    (ContractionCauchyPrimitive.Dolbeault.contractionCauchyPrimitive_smooth χ.contDiff χ.hasCompactSupport hsupp (n + 1) a).mono
      (prod_mono Subset.rfl (subset_univ _))
  let u := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw (ContractionCauchyPrimitive.Dolbeault.productOpen S W) G hG
  have hup : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q u := by
    intro y z v
    exact ContractionCauchyPrimitive.Dolbeault.contractionCauchyPrimitive_pure χ.contDiff χ.hasCompactSupport hsupp
      (n + 1) p q hn a hpure y y.property.1 z v
  have har : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) ar = 0 := by
    rw [show ar = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h a from rfl, ← DivisorClass.Chern.DolbeaultZeroKernelMap.openDolbeaultD_restrict, ha, map_zero]
  have hulast : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S W) n (0, 1) u = 0 := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro y
    rw [Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply]
    exact ContractionCauchyPrimitive.Dolbeault.contractionCauchyPrimitive_last_kernel χ.contDiff χ.hasCompactSupport hsupp n a y y.property.1
  refine ⟨W, mem_ball_self (half_pos hR), hWU, u, hup,
    Open.DolbeaultCorrection.correctOpenDolbeaultForm_closed (n + 1) p q hn ar har u hup,
    Open.DolbeaultCorrection.correctOpenDolbeaultForm_pure (n + 1) p q hn ar
      (DivisorClass.Chern.Open.DolbeaultPrime.openFormHasBidegree_restrict h hpure) u hup, ?_, ?_⟩
  · apply Open.DolbeaultCorrection.correctOpenDolbeaultForm_contraction_zero n (0, 1) ar u hulast
    intro y
    rw [show u = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw (ContractionCauchyPrimitive.Dolbeault.productOpen S W) G hG from rfl,
      Closed.FormAntiholomorphicDirections.Dolbeault.vectorAntiDerivative_ofRaw]
    have he := ContractionCauchyPrimitive.Dolbeault.contractionCauchyPrimitive_last_derivative χ.contDiff χ.hasCompactSupport hsupp
      (n + 1) a y y.property.1 (χ.one_of_mem_closedBall (ball_subset_closedBall y.property.2))
    refine he.trans ?_
    change AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) (0, 1) (a.extension y) =
      AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) (0, 1) (a ⟨y, h y.property⟩)
    rw [a.extension_apply ⟨y, h y.property⟩]
  · intro v hv
    have huv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S W) n (v, 0) u = 0 := by
      apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
      intro y
      rw [Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply]
      exact ContractionCauchyPrimitive.Dolbeault.contractionCauchyPrimitive_kernel χ.contDiff χ.hasCompactSupport hsupp n a (v, 0)
        hv y y.property.1
    apply Open.DolbeaultCorrection.correctOpenDolbeaultForm_contraction_zero n (v, 0) ar u huv
    intro y
    rw [show u = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw (ContractionCauchyPrimitive.Dolbeault.productOpen S W) G hG from rfl,
      Closed.FormAntiholomorphicDirections.Dolbeault.vectorAntiDerivative_ofRaw]
    have he := ContractionCauchyPrimitive.Dolbeault.contractionCauchyPrimitive_preserves_direction χ.contDiff χ.hasCompactSupport hsupp
      (n + 1) a ha v hv y y.property.1
    refine he.trans ?_
    have hz := congrArg (fun b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S U) (n + 1) =>
      b ⟨y, h y.property⟩) hv
    simpa only [ar, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_apply, Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply,
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply] using hz.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.HigherFormCoefficientElimination.Dolbeault
