import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Branch Coefficients At -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt.Constructions.BranchCoefficients

noncomputable section

/-!
# RiemannProjectivity: holomorphic branches and their symmetric coefficients

Over an open set of holomorphic regular values, a proper map has finitely
many holomorphic inverse branches. Their symmetric expressions give the
local coefficient functions used in projection equations.
-/

open Set Filter
open scoped _root_.Topology BigOperators

open OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt.Constructions.FiniteBranches

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
variable {X : Type*} [TopologicalSpace X]

def HasHolomorphicInverseAt (a : X → V) (f : X → W) (x : X) : Prop :=
  ∃ e : OpenPartialHomeomorph X W, x ∈ e.source ∧ (e : X → W) = f ∧
    DifferentiableOn ℂ (fun z => a (e.symm z)) e.target

def holomorphicRegularValues (a : X → V) (f : X → W) : Set W :=
  {y | ∀ x, f x = y → HasHolomorphicInverseAt a f x}

theorem isOpen_holomorphicInverseLocus (a : X → V) (f : X → W) :
    IsOpen {x | HasHolomorphicInverseAt a f x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨e, hx, he, hd⟩
  exact mem_of_superset (e.open_source.mem_nhds hx) (fun z hz => ⟨e, hz, he, hd⟩)

theorem isOpen_holomorphicRegularValues (a : X → V) {f : X → W} (hf : IsClosedMap f) :
    IsOpen (holomorphicRegularValues a f) := by
  have heq : holomorphicRegularValues a f = (f '' {x | ¬HasHolomorphicInverseAt a f x})ᶜ := by
    ext y
    simp only [holomorphicRegularValues, mem_ofPred_eq, mem_compl_iff, mem_image,
      not_exists, not_and]
    constructor
    · exact fun h x hx hxy => hx (h x hxy)
    · intro h x hxy
      by_contra hx
      exact h x hx hxy
  rw [heq]
  exact (hf _ (isOpen_holomorphicInverseLocus a f).isClosed_compl).isOpen_compl

theorem holomorphicRegularValues_subset (a : X → V) (f : X → W) :
    holomorphicRegularValues a f ⊆ FiniteBranchesAt.Constructions.FiniteBranches.regularValues f := by
  intro y hy x hxy
  obtain ⟨e, he, hef, _⟩ := hy x hxy
  exact ⟨e, he, hef⟩

/-- A continuous local section coincides locally with the holomorphic inverse. -/
theorem differentiableAt_section (a : X → V) {f : X → W} {b : W → X} {y : W}
    (hb : ContinuousAt b y) (hsection : ∀ᶠ z in 𝓝 y, f (b z) = z)
    (hby : f (b y) = y) (hi : HasHolomorphicInverseAt a f (b y)) :
    DifferentiableAt ℂ (fun z => a (b z)) y := by
  obtain ⟨e, he, hef, hed⟩ := hi
  have hey : y ∈ e.target := by rw [← hby, ← hef]; exact e.map_source he
  have heq : b =ᶠ[𝓝 y] e.symm := by
    filter_upwards [hb (e.open_source.mem_nhds he), hsection] with z hz hzf
    exact (e.left_inv hz).symm.trans (congrArg e.symm ((congrFun hef (b z)).trans hzf))
  exact ((hed y hey).differentiableAt (e.open_target.mem_nhds hey)).congr_of_eventuallyEq
    (heq.mono (fun z hz => congrArg a hz))

/-- All points in nearby fibers are enumerated by finitely many holomorphic
branches, with no repetitions. -/
theorem finite_holomorphic_branches [T2Space X] (a : X → V) {f : X → W} (hf : IsProperMap f)
    {y : W} (hy : y ∈ holomorphicRegularValues a f) :
    ∃ (m : ℕ) (U : Set W) (b : Fin m → W → X), IsOpen U ∧ y ∈ U ∧
      (∀ i, DifferentiableOn ℂ (fun z => a (b i z)) U) ∧
      ∀ z ∈ U, Function.Injective (fun i => b i z) ∧
        ∀ x, f x = z ↔ ∃ i, b i z = x := by
  classical
  have hr := holomorphicRegularValues_subset a f hy
  have hfin := FiniteBranchesAt.Constructions.FiniteBranches.finite_regular_fiber hf hr
  let I := f ⁻¹' {y}
  let : Fintype I := hfin.fintype
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    have heven := FiniteBranchesAt.Constructions.FiniteBranches.evenlyCovered_regular_value hf hr
    let t := heven.toTrivialization
    let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let U := t.baseSet ∩ holomorphicRegularValues a f
    let b : Fin (Fintype.card I) → W → X :=
      fun i z => t.toOpenPartialHomeomorph.symm (z, eI.symm i)
    have hU : IsOpen U := t.open_baseSet.inter (isOpen_holomorphicRegularValues a hf.isClosedMap)
    have hby (i : Fin (Fintype.card I)) (z : W) (hz : z ∈ U) : f (b i z) = z :=
      t.proj_symm_apply' hz.1
    refine ⟨Fintype.card I, U, b, hU, ⟨heven.mem_toTrivialization_baseSet, hy⟩, ?_, ?_⟩
    · intro i z hz
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_section a (t.continuousAt_symm_prodMk_left hz.1)
        (Filter.Eventually.mono (hU.mem_nhds hz) (fun w hw => hby i w hw)) (hby i z hz)
      exact hz.2 (b i z) (hby i z hz)
    · intro z hz
      refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
      · intro i j hij
        have h := congrArg t hij
        have hti : t (b i z) = (z, eI.symm i) := t.apply_symm_apply' hz.1
        have htj : t (b j z) = (z, eI.symm j) := t.apply_symm_apply' hz.1
        rw [hti, htj] at h
        exact eI.symm.injective (congrArg Prod.snd h)
      · intro hx
        refine ⟨eI (t x).2, ?_⟩
        change t.toOpenPartialHomeomorph.symm (z, eI.symm (eI (t x).2)) = x
        rw [eI.symm_apply_apply, ← hx]
        exact t.symm_apply_mk_proj (t.mem_source.mpr (hx ▸ hz.1))
      · rintro ⟨i, rfl⟩
        exact hby i z hz
  · let U := (range f)ᶜ
    have hyU : y ∈ U := by
      rintro ⟨x, hx⟩
      exact hI ⟨⟨x, hx⟩⟩
    refine ⟨0, U, Fin.elim0, hf.isClosedMap.isClosed_range.isOpen_compl, hyU,
      (fun i => Fin.elim0 i), ?_⟩
    intro z hz
    refine ⟨Function.injective_of_subsingleton _, fun x => ?_⟩
    constructor
    · intro hx
      exact False.elim (hz ⟨x, hx⟩)
    · rintro ⟨i, _⟩
      exact Fin.elim0 i

theorem differentiableOn_coeff_prod {ι : Type*} [Fintype ι] {U : Set W}
    (P : ι → W → Polynomial ℂ)
    (hP : ∀ i j, DifferentiableOn ℂ (fun z => (P i z).coeff j) U) (j : ℕ) :
    DifferentiableOn ℂ (fun z => (∏ i, P i z).coeff j) U := by
  classical
  have h : ∀ s : Finset ι, ∀ j, DifferentiableOn ℂ (fun z => (∏ i ∈ s, P i z).coeff j) U := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro j; simpa only [Finset.prod_empty] using differentiableOn_const ((1 : Polynomial ℂ).coeff j)
    | @insert i s hi ih =>
      intro j
      simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
      exact DifferentiableOn.fun_sum (fun q _ => (hP i q.1).mul (ih q.2))
  exact h Finset.univ j

omit [TopologicalSpace X] in
theorem polynomial_of_holomorphic_branches {m : ℕ} (a : X → V) (f : X → W)
    (b : Fin m → W → X) {U : Set W}
    (hb : ∀ i, DifferentiableOn ℂ (fun z => a (b i z)) U)
    (hbij : ∀ z ∈ U, ∀ x, f x = z ↔ ∃ i, b i z = x) (l : V →L[ℂ] ℂ) :
    let P : W → Polynomial ℂ :=
      fun z => ∏ i : Fin m, (Polynomial.X - Polynomial.C (l (a (b i z))))
    (∀ j, DifferentiableOn ℂ (fun z => (P z).coeff j) U) ∧
    ∀ z ∈ U, (P z).Monic ∧
      ∀ c, (P z).eval c = 0 ↔ ∃ x, f x = z ∧ l (a x) = c := by
  classical
  let P : W → Polynomial ℂ := fun z => ∏ i : Fin m, (Polynomial.X - Polynomial.C (l (a (b i z))))
  change (∀ j, DifferentiableOn ℂ (fun z => (P z).coeff j) U) ∧ _
  constructor
  · intro j
    apply differentiableOn_coeff_prod
    intro i k
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> first
      | exact (differentiableOn_const _).sub (l.differentiable.comp_differentiableOn (hb i))
      | exact differentiableOn_const _
  · intro z hz
    refine ⟨Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _), ?_⟩
    intro c
    have heval : (P z).eval c = 0 ↔ ∃ i : Fin m, l (a (b i z)) = c := by
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
      exact exists_congr (fun _ => eq_comm)
    rw [heval]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨b i z, (hbij z hz _).mpr ⟨i, rfl⟩, hi⟩
    · rintro ⟨x, hx, hl⟩
      obtain ⟨i, rfl⟩ := (hbij z hz x).mp hx
      exact ⟨i, hl⟩

/-- The values of a linear coordinate on each nearby fiber are precisely
the roots of a monic polynomial with holomorphic coefficient functions. -/
theorem local_fiber_polynomial [T2Space X] (a : X → V) {f : X → W} (hf : IsProperMap f)
    {y : W} (hy : y ∈ holomorphicRegularValues a f) (l : V →L[ℂ] ℂ) :
    ∃ (U : Set W) (P : W → Polynomial ℂ), IsOpen U ∧ y ∈ U ∧
      (∀ j, DifferentiableOn ℂ (fun z => (P z).coeff j) U) ∧
      ∀ z ∈ U, (P z).Monic ∧
        ∀ c, (P z).eval c = 0 ↔ ∃ x, f x = z ∧ l (a x) = c := by
  obtain ⟨m, U, b, hU, hyU, hb, hbij⟩ := finite_holomorphic_branches a hf hy
  exact ⟨U, _, hU, hyU, polynomial_of_holomorphic_branches a f b hb
    (fun z hz => (hbij z hz).2) l⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt.Constructions.BranchCoefficients
