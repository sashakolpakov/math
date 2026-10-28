import OAI.AlgebraicGeometry.DivisorClass.Chern.ProductDolbeaultDerivatives
import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOneFormCorrection

/-! # One Form Cauchy Elimination -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormCauchyElimination

noncomputable section

section

/-! A genuine Cauchy primitive for one coefficient of an actual closed one-form on a product chart. -/

open _root_.TopologicalSpace _root_.Complex Set _root_.Metric
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def complexProductOpen (S : Opens P) (U : Opens ℂ) : Opens (P × ℂ) :=
  ⟨(S : Set P) ×ˢ (U : Set ℂ), S.isOpen.prod U.isOpen⟩

def oneFormLastCoefficient {S : Opens P} {U : Opens ℂ}
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (complexProductOpen S U) 1) (p : P) (w : ℂ) : ℂ :=
  AntiOneFormCoordinates.oneFormLinear (a.extension (p, w)) (0, 1)

theorem oneFormLastCoefficient_smooth {S : Opens P} {U : Opens ℂ}
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (complexProductOpen S U) 1) :
    ContDiffOn ℝ ∞ (Function.uncurry (oneFormLastCoefficient a)) ((S : Set P) ×ˢ (U : Set ℂ)) :=
  AntiOneFormCoordinates.openOneForm_coefficient_smooth a (0, 1)

variable [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P]

theorem exists_oneForm_coefficient_primitive {S : Opens P} {U : Opens ℂ}
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (complexProductOpen S U) 1) (ha : DolbeaultOpen.openDolbeaultD 1 a = 0)
    {x : ℂ} (hx : x ∈ U) :
    ∃ G : P × ℂ → ℂ, ContDiffOn ℝ ∞ G ((S : Set P) ×ˢ univ) ∧
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
        (∀ p ∈ S, ∀ w ∈ ball x r,
          AntiOneFormCoordinates.antilinearScalarDerivative G (p, w) (0, 1) =
            oneFormLastCoefficient a p w) ∧
        (∀ v : P, (∀ q : complexProductOpen S U, AntiOneFormCoordinates.oneFormLinear (a q) (v, 0) = 0) →
          ∀ q : P × ℂ, q.1 ∈ S → AntiOneFormCoordinates.antilinearScalarDerivative G q (v, 0) = 0) := by
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (U.isOpen.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := R / 2, rOut := R, rIn_pos := half_pos hR, rIn_lt_rOut := half_lt_self hR }
  have hsupp : tsupport χ ⊆ (U : Set ℂ) := by rwa [χ.tsupport_eq]
  let G := ParametricCauchyLocalPrimitive.localizedParametricCauchyTransform χ (oneFormLastCoefficient a)
  have hGs : ContDiffOn ℝ ∞ G ((S : Set P) ×ˢ univ) :=
    ParametricCauchyLocalPrimitive.localizedParametricCauchyTransform_smooth χ.contDiff χ.hasCompactSupport S.isOpen U.isOpen hsupp
      (oneFormLastCoefficient_smooth a)
  refine ⟨G, hGs, R / 2, half_pos hR,
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hR.le))).trans hsub,
    ?_, ?_⟩
  · intro p hp w hw
    have hdiff : DifferentiableAt ℝ G (p, w) :=
      (hGs.contDiffAt ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hp, mem_univ w⟩)).differentiableAt (by simp)
    rw [← ProductDolbeaultDerivatives.complexDbar_product_slice hdiff]
    exact ParametricCauchyLocalPrimitive.localizedParametricCauchyTransform_primitive χ.contDiff χ.hasCompactSupport
      S.isOpen U.isOpen hsupp (oneFormLastCoefficient_smooth a) hp
        (χ.one_of_mem_closedBall (ball_subset_closedBall hw))
  · intro v hv q hq
    apply (ProductDolbeaultDerivatives.antilinearScalarDerivative_eq_zero_iff G q (v, 0)).mpr
    have h := ParametricCauchyLocalPrimitive.localizedParametricCauchyTransform_preserves_holomorphic_direction
      χ.contDiff χ.hasCompactSupport S.isOpen U.isOpen hsupp
      (oneFormLastCoefficient_smooth a) q hq v (fun w hw => ?_)
    · simpa only [Prod.smul_mk, smul_eq_mul, mul_zero] using h
    · have hz := DolbeaultOneFormCorrection.closed_oneForm_zero_coefficient_derivative a ha (v, 0) hv
        ⟨(q.1, w), ⟨hq, hw⟩⟩ (0, 1)
      have hi := (ProductDolbeaultDerivatives.antilinearScalarDerivative_eq_zero_iff
        (Function.uncurry (oneFormLastCoefficient a)) (q.1, w) (v, 0)).mp hz
      simpa only [Prod.smul_mk, smul_eq_mul, mul_zero] using hi

end

/-! Elimination of one coefficient of an actual pure closed form, preserving previously zero coefficients. -/

open _root_.TopologicalSpace _root_.Complex Set _root_.Metric
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P]

omit [NormedSpace ℝ P] [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] in
theorem complexProductOpen_mono {S : Opens P} {U W : Opens ℂ} (h : W ≤ U) :
    complexProductOpen S W ≤ complexProductOpen S U := fun _ hq => ⟨hq.1, h hq.2⟩

theorem exists_oneForm_coefficient_elimination {S : Opens P} {U : Opens ℂ}
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (complexProductOpen S U) 1) (ha : DolbeaultOpen.openDolbeaultD 1 a = 0)
    (hpure : Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) {x : ℂ} (hx : x ∈ U) :
    ∃ W : Opens ℂ, x ∈ W ∧ ∃ h : W ≤ U,
      ∃ g : P × ℂ → ℂ, ∃ hg : ContDiffOn ℝ ∞ g (complexProductOpen S W : Set (P × ℂ)),
        let b := DolbeaultOneFormCorrection.correctDolbeaultOneForm (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (complexProductOpen_mono h) a) g hg
        DolbeaultOpen.openDolbeaultD 1 b = 0 ∧ Open.DolbeaultPrime.OpenFormHasBidegree 0 1 b ∧
          (∀ q : complexProductOpen S W, AntiOneFormCoordinates.oneFormLinear (b q) (0, 1) = 0) ∧
          (∀ v : P, (∀ q : complexProductOpen S U, AntiOneFormCoordinates.oneFormLinear (a q) (v, 0) = 0) →
            ∀ q : complexProductOpen S W, AntiOneFormCoordinates.oneFormLinear (b q) (v, 0) = 0) := by
  obtain ⟨G, hGs, r, hr, hsub, he, hpres⟩ := exists_oneForm_coefficient_primitive a ha hx
  let W : Opens ℂ := ⟨ball x r, isOpen_ball⟩
  have hWU : W ≤ U := hsub
  let h := complexProductOpen_mono (S := S) hWU
  let ar := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h a
  have har : DolbeaultOpen.openDolbeaultD 1 ar = 0 := by
    change DolbeaultOpen.openDolbeaultD 1 (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h a) = 0
    rw [← DolbeaultZeroKernelMap.openDolbeaultD_restrict h a, ha]
    exact (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h).map_zero
  have hGr : ContDiffOn ℝ ∞ G (complexProductOpen S W : Set (P × ℂ)) :=
    hGs.mono (prod_mono Subset.rfl (subset_univ _))
  refine ⟨W, mem_ball_self hr, hWU, G, hGr,
    DolbeaultOneFormCorrection.correctDolbeaultOneForm_closed ar har hGr,
    DolbeaultOneFormCorrection.correctDolbeaultOneForm_pure ar (Open.DolbeaultPrime.openFormHasBidegree_restrict h hpure) hGr, ?_, ?_⟩
  · apply DolbeaultOneFormCorrection.correctDolbeaultOneForm_coefficient_zero ar hGr (0, 1)
    intro q
    have hq := he q.val.1 q.property.1 q.val.2 q.property.2
    change AntiOneFormCoordinates.antilinearScalarDerivative G q (0, 1) = AntiOneFormCoordinates.oneFormLinear (ar q) (0, 1)
    refine hq.trans ?_
    change AntiOneFormCoordinates.oneFormLinear (a.extension q) (0, 1) = AntiOneFormCoordinates.oneFormLinear (a ⟨q, h q.property⟩) (0, 1)
    rw [show a.extension q = a ⟨q, h q.property⟩ from a.extension_apply ⟨q, h q.property⟩]
  · intro v hv q
    rw [DolbeaultOneFormCorrection.correctDolbeaultOneForm_coefficient]
    have hzero : AntiOneFormCoordinates.oneFormLinear (ar q) (v, 0) = 0 := hv ⟨q, h q.property⟩
    rw [hzero, hpres v hv q q.property.1, sub_self]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormCauchyElimination
