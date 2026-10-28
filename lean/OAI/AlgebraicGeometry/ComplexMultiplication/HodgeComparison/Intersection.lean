import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalMaximum
import OAI.Analysis.DifferentialForms.Manifold.LocalPoincare
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
import OAI.Analysis.DifferentialForms.Manifold.PurePullback
import OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection.CM.Construction

noncomputable section

/-! The two degree-one pure de Rham subspaces have zero intersection. -/

open Set Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The scalar function underlying a smooth zero-form is continuous. -/
theorem zeroFormScalar_continuous (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    Continuous (HolomorphicPrimitive.CM.Construction.zeroFormScalar form) := by
  rw [continuous_iff_continuousAt]
  intro x
  let e := chartAt E x
  have hex : x ∈ e.source := mem_chart_source E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hc := (HolomorphicPrimitive.CM.Construction.zeroFormScalar_contDiffAt_inChart form e he (e.map_source hex)).continuousAt
  have hcomp := hc.comp (e.continuousAt hex)
  have heq : HolomorphicPrimitive.CM.Construction.zeroFormScalar form =ᶠ[𝓝 x] (HolomorphicPrimitive.CM.Construction.zeroFormScalar form ∘ e.symm) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hex] with y hy
    exact congrArg (HolomorphicPrimitive.CM.Construction.zeroFormScalar form) (e.left_inv hy).symm
  exact hcomp.congr_of_eventuallyEq heq

/-- Restriction expressed as an actual smooth pullback to the intrinsic open manifold. -/
def restrictSmoothForm (U : Opens M) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U n :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Subtype.val : U → M)
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞))

theorem d_restrictSmoothForm (U : Opens M) (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (restrictSmoothForm U n form) =
      restrictSmoothForm U (n + 1) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) := by
  exact Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback _ _ form

theorem zeroFormScalar_restrict (U : Opens M) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (x : U) :
    HolomorphicPrimitive.CM.Construction.zeroFormScalar (restrictSmoothForm U 0 form) x = HolomorphicPrimitive.CM.Construction.zeroFormScalar form (x : M) := by
  change form (x : M) _ = form (x : M) 0
  congr 1
  exact Subsingleton.elim _ _

/-- The real local Poincare theorem supplies an intrinsic smooth primitive. -/
theorem exists_local_intrinsic_primitive [FiniteDimensional ℝ E]
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1) (x : M) :
    ∃ (U : Opens M), x ∈ U ∧ ∃ primitive : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0,
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = restrictSmoothForm U 1 form.val := by
  have hclosed : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form.val) = 0 := by
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, form.property, map_zero]
  obtain ⟨U, hU, hxU, primitive, hp⟩ := Analysis.DifferentialForms.Manifold.LocalPoincare.manifold_local_poincare ⊤
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form.val) hclosed ⟨x, trivial⟩
  refine ⟨U, hxU, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 primitive, ?_⟩
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, hp, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen,
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen]
  rfl

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem hasManifoldBidegree_restrict (U : Opens M) (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q))
    (ht : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q form.val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U p q (restrictSmoothForm U (p + q) form).val :=
  ht.pullback (Subtype.val : U → M)
    (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ∞))

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [IsScalarTower ℝ ℂ E]
  [IsManifold 𝓘(ℂ, E) ∞ M] in
/-- The local inverse of an open inclusion is holomorphic. -/
theorem complexOpenInverse_contMDiffAt (U : Opens M) (hs : Nonempty U)
    {x : M} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (U.openPartialHomeomorphSubtypeCoe hs).symm x := by
  rw [← ContMDiffAt.subtypeVal_comp_iff]
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact (U.openPartialHomeomorphSubtypeCoe hs).right_inv
    (by simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy)

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [IsScalarTower ℝ ℂ E]
  [IsManifold 𝓘(ℂ, E) ∞ M] in
/-- A holomorphic function on an intrinsic open set has a holomorphic ambient germ. -/
theorem exists_holomorphic_ambient_germ (U : Opens M) {x : M} (hx : x ∈ U)
    (g : U → ℂ) (hg : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ) g) :
    ∃ G : M → ℂ,
      (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) G y) ∧
      ∀ y : U, G y = g y := by
  let hs : Nonempty U := ⟨⟨x, hx⟩⟩
  let e := U.openPartialHomeomorphSubtypeCoe hs
  refine ⟨g ∘ e.symm, ?_, ?_⟩
  · filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact (hg (e.symm y)).comp y
      ((complexOpenInverse_contMDiffAt U hs hy).mdifferentiableAt (by simp))
  · intro y
    exact congrArg g (e.left_inv (by trivial))

/-- If a scalar differential splits into a closed holomorphic form minus an
antiholomorphic form, the scalar locally splits into holomorphic and conjugate
holomorphic functions. -/
theorem local_holomorphic_split_of_d_eq [FiniteDimensional ℝ E]
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 α.val.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 β.val.val)
    (heq : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = α.val - β.val) (x : M) :
    ∃ (U : Opens M), x ∈ U ∧ ∃ h k : U → ℂ,
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ) h ∧
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ) k ∧
      ∀ y : U, HolomorphicPrimitive.CM.Construction.zeroFormScalar form (y : M) = h y + star (k y) := by
  obtain ⟨U, hxU, primitive, hp⟩ := exists_local_intrinsic_primitive α x
  let residual := restrictSmoothForm U 0 form - primitive
  have hr : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d residual = -restrictSmoothForm U 1 β.val := by
    dsimp only [residual]
    rw [map_sub, d_restrictSmoothForm, heq, map_sub, hp]
    abel
  have hpt : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U 1 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive).val := by
    rw [hp]
    exact hasManifoldBidegree_restrict U 1 0 α.val hα
  have hrt : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U 0 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d residual).val := by
    rw [hr]
    exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E U 0 1).neg_mem
      (hasManifoldBidegree_restrict U 0 1 β.val hβ)
  have hct : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U 1 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Conjugation.CM.Construction.conjugateSmoothForm residual)).val := by
    rw [Conjugation.CM.Construction.d_conjugateSmoothForm]
    apply (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr
    exact Conjugation.CM.Construction.conjugateRawForm_antiholomorphic _
      ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp hrt)
  refine ⟨U, hxU, HolomorphicPrimitive.CM.Construction.zeroFormScalar primitive, HolomorphicPrimitive.CM.Construction.zeroFormScalar (Conjugation.CM.Construction.conjugateSmoothForm residual),
    HolomorphicPrimitive.CM.Construction.zeroFormScalar_mdifferentiable primitive hpt,
    HolomorphicPrimitive.CM.Construction.zeroFormScalar_mdifferentiable (Conjugation.CM.Construction.conjugateSmoothForm residual) hct, ?_⟩
  intro y
  have hy := zeroFormScalar_restrict U form y
  change form (y : M) 0 = primitive y 0 + star (star (residual y 0))
  rw [star_star]
  change form (y : M) 0 = primitive y 0 +
    ((restrictSmoothForm U 0 form) y 0 - primitive y 0)
  change (restrictSmoothForm U 0 form) y 0 = form (y : M) 0 at hy
  rw [hy]
  ring

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [IsScalarTower ℝ ℂ E] in
/-- On a compact complex manifold, a function locally expressible as a sum of
a holomorphic and a conjugate-holomorphic function is locally constant. -/
theorem local_holomorphic_split_isLocallyConstant [CompactSpace M]
    {f : M → ℂ} (hf : Continuous f)
    (hl : ∀ x : M, ∃ (U : Opens M), x ∈ U ∧ ∃ h k : U → ℂ,
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ) h ∧
      MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ) k ∧
      ∀ y : U, f (y : M) = h y + star (k y)) : IsLocallyConstant f := by
  have hre : IsLocallyConstant (fun y => (f y).re) := by
    apply LocalMaximum.CM.Construction.locallyRealPartHolomorphic_isLocallyConstant (E := E) (Complex.continuous_re.comp hf)
    intro x
    obtain ⟨U, hxU, h, k, hh, hk, hsplit⟩ := hl x
    obtain ⟨G, hG, hGeq⟩ := exists_holomorphic_ambient_germ U hxU (h + k) (hh.add hk)
    refine ⟨G, hG, ?_⟩
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    have hs := hsplit ⟨y, hy⟩
    have he := hGeq ⟨y, hy⟩
    change (f y).re = (G y).re
    rw [he, hs]
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Pi.add_apply]
  have him : IsLocallyConstant (fun y => (f y).im) := by
    apply LocalMaximum.CM.Construction.locallyRealPartHolomorphic_isLocallyConstant (E := E) (Complex.continuous_im.comp hf)
    intro x
    obtain ⟨U, hxU, h, k, hh, hk, hsplit⟩ := hl x
    have hd : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ)
        (fun y => -Complex.I * (h y - k y)) := mdifferentiable_const.mul (hh.sub hk)
    obtain ⟨G, hG, hGeq⟩ := exists_holomorphic_ambient_germ U hxU
      (fun y => -Complex.I * (h y - k y)) hd
    refine ⟨G, hG, ?_⟩
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    have hs := hsplit ⟨y, hy⟩
    have he := hGeq ⟨y, hy⟩
    change (f y).im = (G y).re
    rw [he, hs]
    simp [Complex.mul_re, sub_eq_add_neg]
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  filter_upwards [hre.eventually_eq x, him.eventually_eq x] with y hyre hyim
  exact Complex.ext hyre hyim

/-- A primitive of a difference of closed forms of opposite types has zero
differential on a compact complex manifold. -/
theorem d_eq_zero_of_holomorphic_sub_antiholomorphic [FiniteDimensional ℝ E]
    [CompactSpace M] (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 α.val.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 β.val.val)
    (heq : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = α.val - β.val) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 :=
  HolomorphicPrimitive.CM.Construction.d_zeroForm_eq_zero_of_locallyConstant form
    (local_holomorphic_split_isLocallyConstant (zeroFormScalar_continuous form)
      (local_holomorphic_split_of_d_eq form α β hα hβ heq))

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A one-form of both pure types is zero already at the level of covectors. -/
theorem oneForm_eq_zero_of_both_types (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (hhol : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 form.val)
    (hanti : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 form.val) : form = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  let z : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have hh := (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangent_action _).mp hhol x z v
  have ha := (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangent_action _).mp hanti x z v
  have heq := hh.symm.trans ha
  have hne : Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 z ≠ Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 z := by
    norm_num [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, z, Complex.ext_iff]
  exact (mul_eq_mul_right_iff.mp heq).resolve_left hne

/-- Equal classes of opposite pure types have zero representatives. -/
theorem opposite_pure_forms_eq_zero_of_class_eq [FiniteDimensional ℝ E] [CompactSpace M]
    (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 α.val.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 β.val.val)
    (hc : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 α = Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 β) :
    α = 0 ∧ β = 0 := by
  obtain ⟨primitive, hp⟩ := (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_eq_iff E M 1 α β).mp hc
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = α.val - β.val at hp
  have hz := d_eq_zero_of_holomorphic_sub_antiholomorphic primitive α β hα hβ hp
  have heq : α.val = β.val := sub_eq_zero.mp (hp.symm.trans hz)
  have hαzero : α.val = 0 := oneForm_eq_zero_of_both_types α.val hα (heq.symm ▸ hβ)
  exact ⟨Subtype.ext hαzero, Subtype.ext (heq.symm.trans hαzero)⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- On a compact complex manifold the degree-one pure de Rham images are disjoint. -/
theorem pureDeRham_one_disjoint [FiniteDimensional ℝ E] [CompactSpace M] :
    Disjoint (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage E M 1 0)
      (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage E M 0 1) := by
  let : IsManifold 𝓘(ℝ, E) ∞ M := Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth
  apply Submodule.disjoint_def.mpr
  intro c hhol hanti
  obtain ⟨α, hα, hαc⟩ := (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff E M 1 0 c).mp hhol
  obtain ⟨β, hβ, hβc⟩ := (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff E M 0 1 c).mp hanti
  have hzero := (opposite_pure_forms_eq_zero_of_class_eq α β hα hβ (hαc.trans hβc.symm)).1
  rw [← hαc, hzero, map_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection.CM.Construction
