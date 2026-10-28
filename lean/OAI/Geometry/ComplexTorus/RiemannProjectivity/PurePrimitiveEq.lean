import OAI.Geometry.ComplexTorus.RiemannProjectivity.ComparisonField
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Pure Primitive Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.PurePrimitiveEq.Constructions.PurePrimitive

noncomputable section

/-!
# RiemannProjectivity: bounded errors of holomorphic primitives

An entire function at bounded distance from a real-linear map has a
complex-linear leading part. Rescaling gives uniform convergence to that
leading part, and the proved holomorphic uniform-limit theorem applies.
-/

open Set Filter
open scoped _root_.Topology

theorem holomorphic_of_bounded_error (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (l : ℂ →L[ℝ] ℂ) (C : ℝ) (hC : ∀ z, ‖F z - l z‖ ≤ C) :
    Differentiable ℂ l := by
  have hlim : TendstoUniformly (fun r : ℝ => fun z : ℂ => r⁻¹ • F (r • z)) l atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [eventually_ge_atTop (max 1 (C / ε) + 1)] with r hr
    have hr0 : 0 < r := by have := le_max_left (1 : ℝ) (C / ε); linarith
    have hCr : C / ε < r := by have := le_max_right (1 : ℝ) (C / ε); linarith
    intro z
    calc
      dist (l z) (r⁻¹ • F (r • z)) = ‖r⁻¹ • (l (r • z) - F (r • z))‖ := by
        rw [dist_eq_norm, smul_sub, map_smul, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
      _ = r⁻¹ * ‖l (r • z) - F (r • z)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
      _ ≤ r⁻¹ * C := mul_le_mul_of_nonneg_left
        (by simpa only [norm_sub_rev] using hC (r • z)) (inv_nonneg.mpr hr0.le)
      _ < ε := by
        rw [inv_mul_eq_div, div_lt_iff₀ hr0]
        simpa only [mul_comm] using (div_lt_iff₀ hε).mp hCr
  apply differentiableOn_univ.mp
  apply hlim.tendstoUniformlyOn.tendstoLocallyUniformlyOn.differentiableOn _ isOpen_univ
  exact Filter.Eventually.of_forall fun r =>
    ((hF.comp (differentiable_id.const_smul r)).const_smul r⁻¹).differentiableOn

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V]

/-- A bounded error cannot change the complex-linearity of the leading covector. -/
theorem complexLinear_of_bounded_error (F : V → ℂ) (hF : Differentiable ℂ F)
    (l : V →L[ℝ] ℂ) (C : ℝ) (hC : ∀ z, ‖F z - l z‖ ≤ C) :
    ∃ L : V →L[ℂ] ℂ, L.restrictScalars ℝ = l := by
  have hsmul (a : ℂ) (v : V) : l (a • v) = a • l v := by
    let line : ℂ →L[ℂ] V := (ContinuousLinearMap.id ℂ ℂ).smulRight v
    let lv : ℂ →L[ℝ] ℂ := l.comp (line.restrictScalars ℝ)
    have hlv : Differentiable ℂ lv := holomorphic_of_bounded_error (F ∘ line)
      (hF.comp line.differentiable) lv C (fun z => hC (line z))
    have hd : lv = (fderiv ℂ lv 0).restrictScalars ℝ :=
      lv.hasFDerivAt.unique ((hlv 0).hasFDerivAt.restrictScalars ℝ)
    have ha := congrArg (fun k : ℂ →L[ℝ] ℂ => k a) hd
    have h1 := congrArg (fun k : ℂ →L[ℝ] ℂ => k 1) hd
    change l (a • v) = fderiv ℂ lv 0 a at ha
    change l ((1 : ℂ) • v) = fderiv ℂ lv 0 1 at h1
    rw [one_smul] at h1
    calc
      l (a • v) = fderiv ℂ lv 0 a := ha
      _ = a • fderiv ℂ lv 0 1 := by rw [← map_smul, smul_eq_mul, mul_one]
      _ = a • l v := congrArg (fun z => a • z) h1.symm
  exact ⟨⟨{ toFun := l, map_add' := l.map_add, map_smul' := hsmul }, l.continuous⟩, rfl⟩

theorem pureOneForm_complexLinear (a : OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue V 1) (ha : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree V 1 0 a) :
    ∃ L : V →L[ℂ] ℂ, L.restrictScalars ℝ =
      AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (fun _ : V => a) 0 := by
  let l := AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (fun _ : V => a) 0
  have hl (z : ℂ) (v : V) : l (z • v) = z • l v := by
    by_cases hz : z = 0
    · simp [hz]
    · have h := ha (Units.mk0 z hz) (fun _ => v)
      simpa only [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Units.val_mk0, pow_one, pow_zero, mul_one,
        smul_eq_mul] using! h
  exact ⟨⟨{ toFun := l, map_add' := l.map_add, map_smul' := hl }, l.continuous⟩, rfl⟩

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

theorem coverForm_hasBidegree {p q : ℕ}
    (a : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus (p + q))
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus p q a) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) p q (TorusCohomology.Constructions.Torus.coverForm Φ a z) := by
  let t : Φ.periodTorus := QuotientAddGroup.mk z
  have heq : TorusCohomology.Constructions.Torus.coverForm Φ a z =
      (a : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus (p + q)).inChart
        (Φ.periodChart t) (Φ.periodChart t t) := by
    rw [TorusCohomology.Constructions.Torus.coverForm_apply]
    ext v
    exact (OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at a (Φ.periodChart t) (Φ.periodChart_mem_atlas t)
      t (Φ.mem_periodChart_source t) v).symm
  rw [heq]
  exact ha _ (Φ.periodChart_mem_atlas t) _ ((Φ.periodChart t).map_source (Φ.mem_periodChart_source t))

/-- A primitive of a closed holomorphic one-form is an actual entire function on the cover. -/
theorem cover_primitive_holomorphic
    (a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1)
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0 a.val)
    (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
    (hF : ∀ z, HasFDerivAt F (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (TorusCohomology.Constructions.Torus.coverForm Φ a.val) z) z) :
    Differentiable ℂ F := by
  intro z
  obtain ⟨L, hL⟩ := pureOneForm_complexLinear (TorusCohomology.Constructions.Torus.coverForm Φ a.val z)
    (coverForm_hasBidegree Φ (p := 1) (q := 0) a.val ha z)
  exact (hasFDerivAt_of_restrictScalars ℝ (hF z) hL).differentiableAt

/-- The periodic remainder of the cover primitive forces its invariant part to be holomorphic. -/
theorem exists_holomorphic_primitive_remainder
    (a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1)
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0 a.val) :
    ∃ (F : OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E)) (L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ),
      (∀ z, HasFDerivAt (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
        (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (TorusCohomology.Constructions.Torus.coverForm Φ a.val) z) z) ∧
      ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) - L (z + t) = F z - L z := by
  obtain ⟨F, hF⟩ := TorusCohomology.Constructions.Torus.exists_cover_primitive Φ a
  have hperiod : ∀ z t, t ∈ Φ.periodIntegerLattice →
      fderiv ℝ (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) (z + t) = fderiv ℝ (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) z := by
    intro z t ht
    rw [(hF (z + t)).fderiv, (hF z).fderiv]
    unfold AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear
    rw [TorusCohomology.Constructions.Torus.coverForm_periodic Φ a.val z t ht]
  obtain ⟨l, _, hrem⟩ := PrimitiveEq.Constructions.Primitive.exists_periodic_remainder Φ.periodIntegerLattice
    (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ) (F.smooth.differentiable (by simp)) hperiod
  have hb := (IsZLattice.isCompact_range_of_periodic Φ.periodIntegerLattice
    (fun z => F z - l z) (F.smooth.continuous.sub l.continuous) hrem).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  obtain ⟨L, hL⟩ := complexLinear_of_bounded_error (F : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
    (cover_primitive_holomorphic Φ a ha F hF) l C (fun z => hC _ ⟨z, rfl⟩)
  refine ⟨F, L, hF, ?_⟩
  intro z t ht
  have he (w : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) : L w = l w :=
    congrArg (fun k : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ => k w) hL
  simpa only [he] using hrem z t ht

/-- A closed holomorphic one-form differs from an invariant holomorphic
one-form by an actual exact smooth form on the quotient. -/
theorem holomorphic_form_eq_invariant_mod_exact
    (a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1)
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0 a.val) :
    ∃ (L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ)
      (f : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0),
      OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = a.val - (FormsEq.Constructions.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ)).val := by
  obtain ⟨F, L, hF, hrem⟩ := exists_holomorphic_primitive_remainder Φ a ha
  let G : OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :=
    ⟨fun z => F z - L z, F.smooth.sub (L.restrictScalars ℝ).contDiff⟩
  have hG : ∀ z t, t ∈ Φ.periodIntegerLattice → G (z + t) = G z := hrem
  refine ⟨L, TorusCohomology.Constructions.Torus.descendedZeroForm Φ G hG, ?_⟩
  apply TorusCohomology.Constructions.Torus.coverForm_injective Φ
  rw [TorusCohomology.Constructions.Torus.coverForm_d, TorusCohomology.Constructions.Torus.coverForm_descendedZeroForm, TorusCohomology.Constructions.Torus.coverForm_sub]
  change OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d G.toZeroForm = TorusCohomology.Constructions.Torus.coverForm Φ a.val -
    (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
      (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus)
      (FormsEq.Constructions.Forms.projection_real_smooth Φ) (FormsEq.Constructions.Forms.invariantForm Φ
        (ContinuousAlternatingMap.ofSubsingleton ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ (0 : Fin 1)
          (L.restrictScalars ℝ)))).toNormedSpace
  rw [FormsEq.Constructions.Forms.invariantForm_pullback]
  apply OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro z
  ext v
  have hdG : HasFDerivAt (G : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → ℂ)
      (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (TorusCohomology.Constructions.Torus.coverForm Φ a.val) z - L.restrictScalars ℝ) z :=
    (hF z).sub (L.restrictScalars ℝ).hasFDerivAt
  rw [OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, hdG.fderiv]
  change AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (TorusCohomology.Constructions.Torus.coverForm Φ a.val) z (v 0) - L (v 0) =
    TorusCohomology.Constructions.Torus.coverForm Φ a.val z v - L (v 0)
  congr 1
  exact congrArg (fun form : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 1 => form z v)
    (AlgebraicTopology.DeRham.Comparison.RadialOne.linearOneFormToAlt_altOneFormToLinear (TorusCohomology.Constructions.Torus.coverForm Φ a.val))

/-- The genuine holomorphic de Rham classes are exactly the invariant
complex-linear covectors. -/
theorem invariantH1_holomorphic_iff (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :
    (∃ a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1,
      OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0 a.val ∧
      OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a = FormsEq.Constructions.Forms.invariantH1 Φ l) ↔
    ∃ L : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℂ] ℂ, l = L.restrictScalars ℝ := by
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨L, f, hf⟩ := holomorphic_form_eq_invariant_mod_exact Φ a ha
    have hz : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1
        (a - FormsEq.Constructions.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ)) = 0 :=
      (OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 _).mpr ⟨f, hf⟩
    rw [map_sub, sub_eq_zero, he] at hz
    exact ⟨L, FormsEq.Constructions.Forms.invariantH1_injective Φ hz⟩
  · rintro ⟨L, rfl⟩
    exact ⟨FormsEq.Constructions.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ),
      FormsEq.Constructions.Forms.complex_covector_holomorphic Φ L, rfl⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.PurePrimitiveEq.Constructions.PurePrimitive
