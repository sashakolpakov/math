import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Convex.Join
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-! # Radial One -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialOne

noncomputable section

section

/-!
# The radial primitive of an actual differential one-form

This file uses mathlib's continuous alternating maps and curve integral. The
primitive is the integral along the straight segment from the origin. The
Poincaré statement proved here is the degree-one statement on convex open
subsets of a real normed space; no de Rham comparison is assumed.
-/

open Set _root_.MeasureTheory _root_.ContinuousAlternatingMap Filter
open scoped Interval
open scoped _root_.Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The standard identification of a continuous linear map with an alternating
one-form, pointwise on its domain. -/
def linearOneFormToAlt (form : E → E →L[ℝ] F) : E → E [⋀^Fin 1]→L[ℝ] F :=
  fun x ↦ ofSubsingleton ℝ E F (0 : Fin 1) (form x)

/-- The inverse identification, using mathlib's linear isometry equivalence. -/
def altOneFormToLinear (form : E → E [⋀^Fin 1]→L[ℝ] F) : E → E →L[ℝ] F :=
  fun x ↦ (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).symm (form x)

@[simp]
theorem linearOneFormToAlt_apply (form : E → E →L[ℝ] F) (x : E) (v : Fin 1 → E) :
    linearOneFormToAlt form x v = form x (v 0) := by
  simp [linearOneFormToAlt]

@[simp]
theorem linearOneFormToAlt_altOneFormToLinear (form : E → E [⋀^Fin 1]→L[ℝ] F) :
    linearOneFormToAlt (altOneFormToLinear form) = form := by
  funext x
  exact (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).apply_symm_apply (form x)

/-- For a genuine alternating one-form, being closed is exactly the usual
symmetry condition on the derivative of its continuous-linear-map description. -/
theorem extDeriv_linearOneFormToAlt_apply (form : E → E →L[ℝ] F)
    (x : E) (v : Fin 2 → E) :
    extDeriv (linearOneFormToAlt form) x v =
      fderiv ℝ form x (v 0) (v 1) - fderiv ℝ form x (v 1) (v 0) := by
  let e := ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)
  change alternatizeUncurryFin (fderiv ℝ (e ∘ form) x) v = _
  rw [e.comp_fderiv, alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp [e, ofSubsingletonLIE, Fin.removeNth, Fin.tail, sub_eq_add_neg]

theorem extDeriv_linearOneFormToAlt_eq_zero_iff (form : E → E →L[ℝ] F) (x : E) :
    extDeriv (linearOneFormToAlt form) x = 0 ↔
      ∀ u v, fderiv ℝ form x u v = fderiv ℝ form x v u := by
  constructor
  · intro h u v
    have heval := congrArg (fun η : E [⋀^Fin 2]→L[ℝ] F ↦ η ![u, v]) h
    simpa [extDeriv_linearOneFormToAlt_apply, sub_eq_zero] using heval
  · intro h
    ext v
    simp [extDeriv_linearOneFormToAlt_apply, h]

theorem differentiableOn_altOneFormToLinear {s : Set E}
    {form : E → E [⋀^Fin 1]→L[ℝ] F} (hform : DifferentiableOn ℝ form s) :
    DifferentiableOn ℝ (altOneFormToLinear form) s := by
  exact (LinearIsometryEquiv.comp_differentiableOn_iff
    (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).symm).mpr hform

theorem contDiffOn_altOneFormToLinear {s : Set E}
    {form : E → E [⋀^Fin 1]→L[ℝ] F} (hform : ContDiffOn ℝ ∞ form s) :
    ContDiffOn ℝ ∞ (altOneFormToLinear form) s := by
  exact ((ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (0 : Fin 1)).symm.contDiff).comp_contDiffOn hform

theorem symmetric_fderiv_altOneFormToLinear
    {form : E → E [⋀^Fin 1]→L[ℝ] F} {x : E} (hclosed : extDeriv form x = 0) :
    ∀ u v, fderiv ℝ (altOneFormToLinear form) x u v =
      fderiv ℝ (altOneFormToLinear form) x v u := by
  apply (extDeriv_linearOneFormToAlt_eq_zero_iff _ _).mp
  simpa using hclosed

/-- Integration of a one-form along the radial segment. -/
def radialPrimitive (form : E → E →L[ℝ] F) (x : E) : F :=
  curveIntegral form (Path.segment 0 x)

theorem radialPrimitive_eq_integral (form : E → E →L[ℝ] F) (x : E) :
    radialPrimitive form x = ∫ t in (0 : ℝ)..1, form (t • x) x := by
  simp [radialPrimitive, curveIntegral_segment, AffineMap.lineMap_apply]

@[simp]
theorem radialPrimitive_zero (form : E → E →L[ℝ] F) : radialPrimitive form 0 = 0 := by
  simp [radialPrimitive]

theorem norm_radialPrimitive_le (form : E → E →L[ℝ] F) (x : E) {C : ℝ}
    (h : ∀ z ∈ segment ℝ (0 : E) x, ‖form z‖ ≤ C) :
    ‖radialPrimitive form x‖ ≤ C * ‖x‖ := by
  simpa [radialPrimitive] using norm_curveIntegral_segment_le («ω» := form) h

variable [CompleteSpace F]

/-- The radial formula is an actual primitive of a differentiable closed
one-form on a convex domain containing the origin. -/
theorem hasFDerivWithinAt_radialPrimitive
    {s : Set E} {form : E → E →L[ℝ] F} {dform : E → E →L[ℝ] E →L[ℝ] F}
    (hs : Convex ℝ s) (hzero : (0 : E) ∈ s)
    (hform : ∀ x ∈ s, HasFDerivWithinAt form (dform x) s x)
    (hclosed : ∀ a ∈ s, ∀ u ∈ tangentConeAt ℝ s a,
      ∀ v ∈ tangentConeAt ℝ s a, dform a u v = dform a v u)
    {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt (radialPrimitive form) (form x) s x := by
  exact hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    hform hclosed hzero hx

theorem hasFDerivAt_radialPrimitive
    {s : Set E} {form : E → E →L[ℝ] F}
    (hs : Convex ℝ s) (hopen : IsOpen s) (hzero : (0 : E) ∈ s)
    (hform : DifferentiableOn ℝ form s)
    (hclosed : ∀ a ∈ s, ∀ u v, fderiv ℝ form a u v = fderiv ℝ form a v u)
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (radialPrimitive form) (form x) x := by
  apply (hasFDerivWithinAt_radialPrimitive hs hzero
    (dform := fun a ↦ fderiv ℝ form a) ?_ ?_ hx).hasFDerivAt (hopen.mem_nhds hx)
  · intro a ha
    exact (hform.differentiableAt (hopen.mem_nhds ha)).hasFDerivAt.hasFDerivWithinAt
  · intro a ha u _ v _
    exact hclosed a ha u v

/-- Every point of an open star-shaped set has a convex neighborhood inside
that set which also contains the star center. The neighborhood need not be
open at the center. -/
theorem exists_convex_neighborhood_with_origin
    {s : Set E} (hstar : StarConvex ℝ (0 : E) s) (hopen : IsOpen s)
    {x : E} (hx : x ∈ s) :
    ∃ t : Set E, Convex ℝ t ∧ (0 : E) ∈ t ∧ t ⊆ s ∧ t ∈ 𝓝 x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  let t := convexJoin ℝ ({0} : Set E) (Metric.ball x r)
  have hbt : Metric.ball x r ⊆ t := subset_convexJoin_right (singleton_nonempty 0)
  refine ⟨t, (convex_singleton 0).convexJoin (convex_ball x r), ?_, ?_, ?_⟩
  · exact subset_convexJoin_left ⟨x, Metric.mem_ball_self hr⟩ (mem_singleton 0)
  · intro z hz
    obtain ⟨a, ha, b, hb, hab⟩ := mem_convexJoin.mp hz
    have ha0 : a = 0 := mem_singleton_iff.mp ha
    subst a
    exact hstar.segment_subset (hball hb) hab
  · exact mem_of_superset (Metric.ball_mem_nhds x hr) hbt

/-- Degree-one radial Poincaré lemma on an open star-shaped domain. -/
theorem hasFDerivAt_radialPrimitive_star
    {s : Set E} {form : E → E →L[ℝ] F}
    (hstar : StarConvex ℝ (0 : E) s) (hopen : IsOpen s)
    (hform : DifferentiableOn ℝ form s)
    (hclosed : ∀ a ∈ s, ∀ u v, fderiv ℝ form a u v = fderiv ℝ form a v u)
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (radialPrimitive form) (form x) x := by
  obtain ⟨t, ht, hzero, hts, htx⟩ := exists_convex_neighborhood_with_origin hstar hopen hx
  have hxt : x ∈ t := mem_of_mem_nhds htx
  apply (hasFDerivWithinAt_radialPrimitive ht hzero
    (dform := fun a ↦ fderiv ℝ form a) ?_ ?_ hxt).hasFDerivAt htx
  · intro a ha
    exact (hform.differentiableAt (hopen.mem_nhds (hts ha))).hasFDerivAt.hasFDerivWithinAt
  · intro a ha u _ v _
    exact hclosed a (hts ha) u v

/-- The radial primitive of a smooth closed one-form is smooth on the same
open star-shaped domain. -/
theorem contDiffOn_radialPrimitive_star
    {s : Set E} {form : E → E →L[ℝ] F}
    (hstar : StarConvex ℝ (0 : E) s) (hopen : IsOpen s)
    (hform : ContDiffOn ℝ ∞ form s)
    (hclosed : ∀ a ∈ s, ∀ u v, fderiv ℝ form a u v = fderiv ℝ form a v u) :
    ContDiffOn ℝ ∞ (radialPrimitive form) s := by
  have hderiv : ∀ x ∈ s, HasFDerivAt (radialPrimitive form) (form x) x :=
    fun x hx ↦ hasFDerivAt_radialPrimitive_star hstar hopen
      (hform.differentiableOn (by simp)) hclosed hx
  apply (contDiffOn_infty_iff_fderiv_of_isOpen hopen).mpr
  constructor
  · exact fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt
  · exact (contDiffOn_congr fun x hx ↦ (hderiv x hx).fderiv).mpr hform

/-- In the actual alternating-form API, the exterior derivative of the radial
zero-form is the given one-form. -/
theorem extDeriv_radialPrimitive
    {s : Set E} {form : E → E →L[ℝ] F}
    (hs : Convex ℝ s) (hopen : IsOpen s) (hzero : (0 : E) ∈ s)
    (hform : DifferentiableOn ℝ form s)
    (hclosed : ∀ a ∈ s, ∀ u v, fderiv ℝ form a u v = fderiv ℝ form a v u)
    {x : E} (hx : x ∈ s) :
    extDeriv (fun a ↦ constOfIsEmpty ℝ E (Fin 0) (radialPrimitive form a)) x =
      linearOneFormToAlt form x := by
  rw [extDeriv_constOfIsEmpty,
    (hasFDerivAt_radialPrimitive hs hopen hzero hform hclosed hx).fderiv]
  rfl

/-- Degree-one Poincaré lemma in the actual alternating-form representation:
the explicitly integrated zero-form has exterior derivative `form` on the domain. -/
theorem extDeriv_radialPrimitive_of_closed
    {s : Set E} {form : E → E [⋀^Fin 1]→L[ℝ] F}
    (hs : Convex ℝ s) (hopen : IsOpen s) (hzero : (0 : E) ∈ s)
    (hform : DifferentiableOn ℝ form s)
    (hclosed : ∀ a ∈ s, extDeriv form a = 0)
    {x : E} (hx : x ∈ s) :
    extDeriv (fun a ↦ constOfIsEmpty ℝ E (Fin 0)
      (radialPrimitive (altOneFormToLinear form) a)) x = form x := by
  have hsymmetric : ∀ a ∈ s, ∀ u v,
      fderiv ℝ (altOneFormToLinear form) a u v =
        fderiv ℝ (altOneFormToLinear form) a v u := by
    intro a ha
    apply (extDeriv_linearOneFormToAlt_eq_zero_iff _ _).mp
    simpa using hclosed a ha
  simpa using extDeriv_radialPrimitive hs hopen hzero
    (differentiableOn_altOneFormToLinear hform) hsymmetric hx

/-- The actual exterior derivative of the radial zero-form recovers a closed
one-form on every open star-shaped domain. -/
theorem extDeriv_radialPrimitive_of_closed_star
    {s : Set E} {form : E → E [⋀^Fin 1]→L[ℝ] F}
    (hstar : StarConvex ℝ (0 : E) s) (hopen : IsOpen s)
    (hform : DifferentiableOn ℝ form s)
    (hclosed : ∀ a ∈ s, extDeriv form a = 0)
    {x : E} (hx : x ∈ s) :
    extDeriv (fun a ↦ constOfIsEmpty ℝ E (Fin 0)
      (radialPrimitive (altOneFormToLinear form) a)) x = form x := by
  rw [extDeriv_constOfIsEmpty]
  rw [(hasFDerivAt_radialPrimitive_star hstar hopen
    (differentiableOn_altOneFormToLinear hform)
    (fun a ha ↦ symmetric_fderiv_altOneFormToLinear (hclosed a ha)) hx).fderiv]
  exact congrFun (linearOneFormToAlt_altOneFormToLinear form) x

theorem contDiffOn_radialPrimitive_of_closed_star
    {s : Set E} {form : E → E [⋀^Fin 1]→L[ℝ] F}
    (hstar : StarConvex ℝ (0 : E) s) (hopen : IsOpen s)
    (hform : ContDiffOn ℝ ∞ form s)
    (hclosed : ∀ a ∈ s, extDeriv form a = 0) :
    ContDiffOn ℝ ∞ (radialPrimitive (altOneFormToLinear form)) s := by
  exact contDiffOn_radialPrimitive_star hstar hopen (contDiffOn_altOneFormToLinear hform)
    (fun a ha ↦ symmetric_fderiv_altOneFormToLinear (hclosed a ha))

end

section

/-!
# Radial homotopy operator on continuous differential forms

The degree-lowering operator is defined by its usual Bochner integral in the
space of actual continuous alternating maps. Its full homotopy identity in
higher degree is not asserted here; the degree-one Poincaré identity is proved
in `RadialOneForm`.
-/

open _root_.MeasureTheory _root_.ContinuousAlternatingMap
open scoped Interval

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

/-- The standard radial integrand: contraction with the radial vector, with
the degree-dependent power coming from pullback under dilation. -/
def radialIntegrand (form : E → E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) (t : ℝ) :
    E [⋀^Fin n]→L[ℝ] F :=
  t ^ n • (form (t • x)).curryLeft x

/-- The usual radial homotopy operator, lowering degree by one. -/
def radialHomotopy (form : E → E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    E [⋀^Fin n]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, radialIntegrand form x t

theorem continuous_radialIntegrand
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : Continuous form) (x : E) :
    Continuous (radialIntegrand form x) := by
  have hradial : Continuous (fun t : ℝ ↦ form (t • x)) :=
    hform.comp (continuous_id.smul continuous_const)
  have hcurry : Continuous (fun t : ℝ ↦ (form (t • x)).curryLeft) :=
    curryLeftLI.continuous.comp hradial
  exact (continuous_pow n).smul (hcurry.clm_apply continuous_const)

theorem intervalIntegrable_radialIntegrand
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : Continuous form) (x : E) :
    IntervalIntegrable (radialIntegrand form x) volume 0 1 :=
  (continuous_radialIntegrand hform x).intervalIntegrable 0 1

variable [CompleteSpace F]

/-- Evaluation of the operator gives the standard coordinate-free integral
formula, so the operator is not an abstract replacement for a homotopy. -/
theorem radialHomotopy_apply
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : Continuous form)
    (x : E) (v : Fin n → E) :
    radialHomotopy form x v =
      ∫ t in (0 : ℝ)..1, t ^ n • form (t • x) (Matrix.vecCons x v) := by
  have h := (ContinuousAlternatingMap.apply ℝ E F v).intervalIntegral_comp_comm
    (intervalIntegrable_radialIntegrand hform x)
  simpa [radialHomotopy, radialIntegrand] using h.symm

end

/-!
# Alternating-map identities for the radial homotopy

These are algebraic identities for actual continuous alternating maps, used
to prove the radial homotopy formula without assuming Cartan's formula.
-/

open _root_.ContinuousAlternatingMap

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

/-- Contract the alternating output of a derivative with a fixed vector. -/
def contractionDerivative
    (f : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    E →L[ℝ] E [⋀^Fin n]→L[ℝ] F :=
  ((curryLeftLI : (E [⋀^Fin (n + 1)]→L[ℝ] F) →ₗᵢ[ℝ]
    (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F)).toContinuousLinearMap.comp f).flip x

@[simp]
theorem contractionDerivative_apply
    (f : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] F) (x y : E) (v : Fin n → E) :
    contractionDerivative f x y v = f y (Matrix.vecCons x v) := rfl

/-- The algebraic cancellation at the heart of the radial Cartan identity. -/
theorem alternatize_contractionDerivative_add
    (f : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    alternatizeUncurryFin (contractionDerivative f x) +
      (alternatizeUncurryFin f).curryLeft x = f x := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, alternatizeUncurryFin_apply, contractionDerivative_apply,
    curryLeft_apply_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hzero : (0 : Fin (n + 2)).removeNth (Matrix.vecCons x v) = v := rfl
  have hsucc (i : Fin (n + 1)) :
      i.succ.removeNth (Matrix.vecCons x v) = Matrix.vecCons x (i.removeNth v) := by
    exact Fin.cons_comp_succ_succAbove x v i
  simp only [hzero, hsucc, pow_succ, mul_smul, neg_one_zsmul, zsmul_neg]
  simp only [neg_neg, pow_zero, one_zsmul, Finset.sum_neg_distrib]
  abel

/-- The same cancellation with the degree weights from radial dilation. -/
theorem weighted_alternatize_contractionDerivative_add
    (a : E [⋀^Fin (n + 1)]→L[ℝ] F)
    (f : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) (t : ℝ) :
    alternatizeUncurryFin (t ^ n • (a.curryLeft + t • contractionDerivative f x)) +
        t ^ (n + 1) • (alternatizeUncurryFin f).curryLeft x =
      ((n + 1 : ℝ) * t ^ n) • a + t ^ (n + 1) • f x := by
  rw [alternatizeUncurryFin_smul, alternatizeUncurryFin_add,
    alternatizeUncurryFin_smul, alternatizeUncurryFin_curryLeft,
    ← Nat.cast_smul_eq_nsmul ℝ]
  calc
    _ = ((n + 1 : ℝ) * t ^ n) • a +
        t ^ (n + 1) • (alternatizeUncurryFin (contractionDerivative f x) +
          (alternatizeUncurryFin f).curryLeft x) := by
      simp only [smul_add, smul_smul, pow_succ]
      module
    _ = _ := by rw [alternatize_contractionDerivative_add]

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
