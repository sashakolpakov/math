import OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms
import Mathlib.Topology.ContinuousOn

/-! # Logarithms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.Logarithms.Construction

noncomputable section

section

/-!
# ChernClass: continuous logarithms on ambient open neighborhoods

This packages the explicit local complex logarithm on a smaller open subset
of the original space, rather than only on a subtype of an open subset.
-/

open _root_.TopologicalSpace

variable {T : Type*} [TopologicalSpace T]

/-- Actual local logarithm data, including the elementary exponential identity. -/
structure OpenLogarithm (D : Opens T) (g : C(D, ℂ)) (p : D) where
  domain : Opens T
  subset : domain ≤ D
  mem_domain : p.val ∈ domain
  logarithm : C(domain, ℂ)
  exp_logarithm : ∀ q : domain,
    Complex.exp (logarithm q) = g ⟨q.val, subset q.property⟩

/-- The local logarithm is constructed by rotating the slit plane to g(p). -/
def openLogarithm (D : Opens T) (g : C(D, ℂ)) (p : D) (hp : g p ≠ 0) :
    OpenLogarithm D g p := by
  classical
  let F : T → ℂ := fun x => if hx : x ∈ D then g ⟨x, hx⟩ else 0
  have hF : ContinuousOn F (D : Set T) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : D => F x.val)
    have heq : (fun x : D => F x.val) = g := by
      funext x
      exact dite_eq_left x.property
    rw [heq]
    exact g.continuous
  let S : Set T := (D : Set T) ∩ (fun x => F x / g p) ⁻¹' Complex.slitPlane
  have hS : IsOpen S :=
    (hF.div_const (g p)).isOpen_inter_preimage D.isOpen Complex.isOpen_slitPlane
  have hpS : p.val ∈ S := by
    refine ⟨p.property, ?_⟩
    change F p.val / g p ∈ Complex.slitPlane
    simp only [F, dite_eq_left p.property, div_self hp, Complex.one_mem_slitPlane]
  have hlog : ContinuousOn (fun x => Complex.log (F x / g p) + Complex.log (g p)) S :=
    (((hF.mono Set.inter_subset_left).div_const (g p)).clog (fun _ hx => hx.2)).add
      continuousOn_const
  refine {
    domain := ⟨S, hS⟩
    subset := Set.inter_subset_left
    mem_domain := hpS
    logarithm := ⟨fun x => Complex.log (F x.val / g p) + Complex.log (g p),
      continuousOn_iff_continuous_domRestrict.mp hlog⟩
    exp_logarithm := ?_ }
  intro q
  change Complex.exp (Complex.log (F q.val / g p) + Complex.log (g p)) = _
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero q.property.2),
    Complex.exp_log hp, div_mul_cancel₀ _ hp]
  exact dite_eq_left q.property.1

end

/-!
# ChernClass: local logarithms of nonvanishing changes of frame

Refining each chart near each of its points gives continuous logarithms of a
nonvanishing continuous section on every refined chart.
-/

open _root_.TopologicalSpace

variable {T I : Type} [TopologicalSpace T]

/-- Logarithmic refinement for a family of nonvanishing functions on charts. -/
structure SectionLogRefinement (U : I → Opens T) (g : ∀ i, C(U i, ℂ)) where
  cover : (Σ i, U i) → Opens T
  subset : ∀ a, cover a ≤ U a.1
  logarithm : ∀ a, C(cover a, ℂ)
  exp_logarithm : ∀ a (x : cover a),
    Complex.exp (logarithm a x) = g a.1 ⟨x.val, subset a x.property⟩
  contains_center : ∀ a, a.2.val ∈ cover a

/-- Each refined chart uses the explicit slit-plane logarithm at its center. -/
def sectionLogRefinement (U : I → Opens T) (g : ∀ i, C(U i, ℂ))
    (hg : ∀ i x, g i x ≠ 0) : SectionLogRefinement U g where
  cover a := (openLogarithm (U a.1) (g a.1) a.2 (hg a.1 a.2)).domain
  subset a := (openLogarithm (U a.1) (g a.1) a.2 (hg a.1 a.2)).subset
  logarithm a := (openLogarithm (U a.1) (g a.1) a.2 (hg a.1 a.2)).logarithm
  exp_logarithm a := (openLogarithm (U a.1) (g a.1) a.2 (hg a.1 a.2)).exp_logarithm
  contains_center a := (openLogarithm (U a.1) (g a.1) a.2 (hg a.1 a.2)).mem_domain

theorem sectionLogRefinement_covers (U : I → Opens T) (g : ∀ i, C(U i, ℂ))
    (hg : ∀ i x, g i x ≠ 0) (hc : ∀ x, ∃ i, x ∈ U i) :
    ∀ x, ∃ a, x ∈ (sectionLogRefinement U g hg).cover a := by
  intro x
  obtain ⟨i, hi⟩ := hc x
  exact ⟨⟨i, ⟨x, hi⟩⟩, (sectionLogRefinement U g hg).contains_center ⟨i, ⟨x, hi⟩⟩⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.Logarithms.Construction
