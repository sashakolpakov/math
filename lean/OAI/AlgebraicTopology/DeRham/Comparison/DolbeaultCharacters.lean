import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDegreeTransport

/-! # Dolbeault Characters -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultCharacters

noncomputable section

section

/-!
# Actual bidegrees and common-degree scalar characters

These lemmas translate the existing geometric pure-type predicate into the
literal inverse-scalar action on actual tangent covectors. Degree changes are
only transports along proved equalities and introduce no sign or permutation.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Filter

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {p q n m : ℕ}

/-- The actual geometric pure-type condition gives the inverse scalar character. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.complexAction_eq {form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)}
    (hform : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q form) (z : ℂˣ) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z form = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z⁻¹ • form := by
  have h := (Analysis.DifferentialForms.Manifold.CovectorAction.hasTangentBidegree_iff_section_action form).mp
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree form).mp hform) z
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter_inv] using h

namespace RawManifoldForm

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_castDegree (h : n = m) (z : ℂˣ) (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree h form) = Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree h (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z form) := by
  cases h
  rfl

end RawManifoldForm

namespace SmoothManifoldForm

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction_castDegree (h : n = m) (z : ℂˣ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h form) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z form) := by
  cases h
  rfl

end SmoothManifoldForm

/-- Transport to a common total degree preserves the literal geometric character. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.complexAction_castDegree
    {form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)} (hform : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q form)
    (h : p + q = n) (z : ℂˣ) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree h form) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z⁻¹ • Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree h form := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_castDegree, hform.complexAction_eq,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree_smul]

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
/-- The chart character at any equal degree is exactly the existing pure-type predicate. -/
theorem hasManifoldBidegree_castDegree_iff (h : n = p + q) (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree h form) ↔
      ∀ e ∈ atlas E M, ∀ y ∈ e.target, ∀ (z : ℂˣ) (v : Fin n → E),
        form.inChart e y (fun i => (z : ℂ) • v i) =
          Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * form.inChart e y v := by
  cases h
  rfl

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
/-- A pure global form has pure chart values on an actual neighborhood of every chart point. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.eventually_hasBidegree_inChart (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    ∀ᶠ y' in 𝓝 y, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e y') := by
  filter_upwards [e.open_target.mem_nhds hy] with y' hy'
  exact form.hasBidegree_inChart e he hy'

end

/-!
# Equality transport for iterated actual Dolbeault operators

Only equality of natural-number degree indices is used. The covectors,
their tangent arguments, and their exterior derivatives remain unchanged.
-/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n m k : ℕ}

namespace RawManifoldForm

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree_zero (h : n = m) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree h (0 : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) = 0 := by
  cases h
  rfl

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree_eq_zero_iff (h : n = m) (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree h form = 0 ↔ form = 0 := by
  cases h
  rfl

theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree_injective (h : n = m) :
    Function.Injective (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree (E := E) (M := M) h) := by
  cases h
  intro form other heq
  exact heq

end RawManifoldForm

namespace SmoothManifoldForm

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_zero (h : n = m) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h (0 : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) = 0 := by
  cases h
  rfl

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_eq_zero_iff (h : n = m) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h form = 0 ↔ form = 0 := by
  cases h
  rfl

theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_injective (h : n = m) :
    Function.Injective (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (E := E) (M := M) h) := by
  cases h
  intro form other heq
  exact heq

/-- Degree-index transport is the identity linear equivalence on the actual smooth forms. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv (h : n = m) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M m := by
  cases h
  exact LinearEquiv.refl ℂ _

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv_apply (h : n = m) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv h form = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h form := by
  cases h
  rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Transport before and after differentiation has no effect beyond the total degree equality. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_d_castDegree (h : n = m) (g : m + 1 = k) (hg : n + 1 = k)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree g (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree h form)) = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree hg (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_castDegree, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_castDegree]

end SmoothManifoldForm

end

end OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultCharacters
