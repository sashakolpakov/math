import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicForms
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Torus
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalAlgebraic
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Algebraic Pure Primitive -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPurePrimitive.CM.Abelian.Algebraization.PurePrimitive

noncomputable section

/-!
# CMAbelianVariety: bounded errors of holomorphic primitives

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

open OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicForms.CM.Abelian.Algebraization.Forms

variable (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)

theorem coverForm_hasBidegree {p q : ℕ}
    (a : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Φ.space) Φ.periodTorus (p + q))
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus p q a) (z : Φ.space) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (Φ.space) p q (Torus.CM.Abelian.Algebraization.coverForm Φ a z) := by
  let t : Φ.periodTorus := QuotientAddGroup.mk z
  have heq : Torus.CM.Abelian.Algebraization.coverForm Φ a z =
      (a : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (Φ.space) Φ.periodTorus (p + q)).inChart
        (Φ.periodChart t) (Φ.periodChart t t) := by
    rw [Torus.CM.Abelian.Algebraization.coverForm_apply]
    ext v
    exact (OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at a (Φ.periodChart t) (Φ.periodChart_mem_atlas t)
      t (Φ.mem_periodChart_source t) v).symm
  rw [heq]
  exact ha _ (Φ.periodChart_mem_atlas t) _ ((Φ.periodChart t).map_source (Φ.mem_periodChart_source t))

/-- A primitive of a closed holomorphic one-form is an actual entire function on the cover. -/
theorem cover_primitive_holomorphic
    (a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Φ.space) Φ.periodTorus 1)
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 1 0 a.val)
    (F : Φ.space → ℂ)
    (hF : ∀ z, HasFDerivAt F (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (Torus.CM.Abelian.Algebraization.coverForm Φ a.val) z) z) :
    Differentiable ℂ F := by
  intro z
  obtain ⟨L, hL⟩ := pureOneForm_complexLinear (Torus.CM.Abelian.Algebraization.coverForm Φ a.val z)
    (coverForm_hasBidegree Φ (p := 1) (q := 0) a.val ha z)
  exact (hasFDerivAt_of_restrictScalars ℝ (hF z) hL).differentiableAt

/-- The periodic remainder of the cover primitive forces its invariant part to be holomorphic. -/
theorem exists_holomorphic_primitive_remainder
    (a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Φ.space) Φ.periodTorus 1)
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 1 0 a.val) :
    ∃ (F : OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (Φ.space)) (L : Φ.space →L[ℂ] ℂ),
      (∀ z, HasFDerivAt (F : Φ.space → ℂ)
        (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (Torus.CM.Abelian.Algebraization.coverForm Φ a.val) z) z) ∧
      ∀ z t, t ∈ Φ.periodIntegerLattice → F (z + t) - L (z + t) = F z - L z := by
  obtain ⟨F, hF⟩ := Torus.CM.Abelian.Algebraization.exists_cover_primitive Φ a
  have hperiod : ∀ z t, t ∈ Φ.periodIntegerLattice →
      fderiv ℝ (F : Φ.space → ℂ) (z + t) = fderiv ℝ (F : Φ.space → ℂ) z := by
    intro z t ht
    rw [(hF (z + t)).fderiv, (hF z).fderiv]
    unfold AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear
    rw [Torus.CM.Abelian.Algebraization.coverForm_periodic Φ a.val z t ht]
  obtain ⟨l, _, hrem⟩ := Geometry.ComplexTorus.RiemannProjectivity.PrimitiveEq.Constructions.Primitive.exists_periodic_remainder Φ.periodIntegerLattice
    (F : Φ.space → ℂ) (F.smooth.differentiable (by simp)) hperiod
  have hb := (IsZLattice.isCompact_range_of_periodic Φ.periodIntegerLattice
    (fun z => F z - l z) (F.smooth.continuous.sub l.continuous) hrem).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  obtain ⟨L, hL⟩ := complexLinear_of_bounded_error (F : Φ.space → ℂ)
    (cover_primitive_holomorphic Φ a ha F hF) l C (fun z => hC _ ⟨z, rfl⟩)
  refine ⟨F, L, hF, ?_⟩
  intro z t ht
  have he (w : Φ.space) : L w = l w :=
    congrArg (fun k : Φ.space →L[ℝ] ℂ => k w) hL
  simpa only [he] using hrem z t ht

/-- A closed holomorphic one-form differs from an invariant holomorphic
one-form by an actual exact smooth form on the quotient. -/
theorem holomorphic_form_eq_invariant_mod_exact
    (a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Φ.space) Φ.periodTorus 1)
    (ha : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 1 0 a.val) :
    ∃ (L : Φ.space →L[ℂ] ℂ)
      (f : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Φ.space) Φ.periodTorus 0),
      OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = a.val - (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ)).val := by
  obtain ⟨F, L, hF, hrem⟩ := exists_holomorphic_primitive_remainder Φ a ha
  let G : OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction (Φ.space) :=
    ⟨fun z => F z - L z, F.smooth.sub (L.restrictScalars ℝ).contDiff⟩
  have hG : ∀ z t, t ∈ Φ.periodIntegerLattice → G (z + t) = G z := hrem
  refine ⟨L, Torus.CM.Abelian.Algebraization.descendedZeroForm Φ G hG, ?_⟩
  apply Torus.CM.Abelian.Algebraization.coverForm_injective Φ
  rw [Torus.CM.Abelian.Algebraization.coverForm_d, Torus.CM.Abelian.Algebraization.coverForm_descendedZeroForm, Torus.CM.Abelian.Algebraization.coverForm_sub]
  change OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d G.toZeroForm = Torus.CM.Abelian.Algebraization.coverForm Φ a.val -
    (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
      (QuotientAddGroup.mk : Φ.space → Φ.periodTorus)
      (AlgebraicForms.CM.Abelian.Algebraization.Forms.projection_real_smooth Φ) (AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantForm Φ
        (ContinuousAlternatingMap.ofSubsingleton ℝ (Φ.space) ℂ (0 : Fin 1)
          (L.restrictScalars ℝ)))).toNormedSpace
  rw [AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantForm_pullback]
  apply OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro z
  ext v
  have hdG : HasFDerivAt (G : Φ.space → ℂ)
      (AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (Torus.CM.Abelian.Algebraization.coverForm Φ a.val) z - L.restrictScalars ℝ) z :=
    (hF z).sub (L.restrictScalars ℝ).hasFDerivAt
  rw [OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply, hdG.fderiv]
  change AlgebraicTopology.DeRham.Comparison.RadialOne.altOneFormToLinear (Torus.CM.Abelian.Algebraization.coverForm Φ a.val) z (v 0) - L (v 0) =
    Torus.CM.Abelian.Algebraization.coverForm Φ a.val z v - L (v 0)
  congr 1
  exact congrArg (fun form : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm (Φ.space) 1 => form z v)
    (AlgebraicTopology.DeRham.Comparison.RadialOne.linearOneFormToAlt_altOneFormToLinear (Torus.CM.Abelian.Algebraization.coverForm Φ a.val))

/-- The genuine holomorphic de Rham classes are exactly the invariant
complex-linear covectors. -/
theorem invariantH1_holomorphic_iff (l : Φ.space →L[ℝ] ℂ) :
    (∃ a : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Φ.space) Φ.periodTorus 1,
      OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Φ.space) Φ.periodTorus 1 0 a.val ∧
      OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Φ.space) Φ.periodTorus 1 a = AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantH1 Φ l) ↔
    ∃ L : Φ.space →L[ℂ] ℂ, l = L.restrictScalars ℝ := by
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨L, f, hf⟩ := holomorphic_form_eq_invariant_mod_exact Φ a ha
    have hz : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Φ.space) Φ.periodTorus 1
        (a - AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ)) = 0 :=
      (OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (Φ.space) Φ.periodTorus 1 _).mpr ⟨f, hf⟩
    rw [map_sub, sub_eq_zero, he] at hz
    exact ⟨L, AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantH1_injective Φ hz⟩
  · rintro ⟨L, rfl⟩
    exact ⟨AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantClosedOneForm Φ (L.restrictScalars ℝ),
      AlgebraicForms.CM.Abelian.Algebraization.Forms.complex_covector_holomorphic Φ L, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPurePrimitive.CM.Abelian.Algebraization.PurePrimitive
