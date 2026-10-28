import OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultProjection
import OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultCharacters
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal

/-! # Manifold Dolbeault -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeault

noncomputable section

/-!
# Actual global Dolbeault operators on pure manifold forms

The smooth scalar-action projections are identified in every holomorphic
chart with alternation of the complex-linear and conjugate-linear parts of
the real derivative. The full character theorem proves their exact raised
bidegrees. Thus these are operators on the existing genuine pure-form
submodules, and their sum is the actual exterior derivative.
-/

open scoped _root_.Manifold ContDiff _root_.Topology

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {p q : ℕ}

section

/-- Every actual holomorphic chart identifies the global prime projection
with the ordinary local `d'` formula. -/
theorem manifoldDolbeaultPrimeForm_eq_local (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    (DolbeaultProjection.manifoldDolbeaultPrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)).inChart e y =
      Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e) y := by
  rw [DolbeaultProjection.manifoldDolbeaultPrimeForm_inChart p q form e he hy]
  let f : Analysis.DifferentialForms.Manifold.Basic.RawForm E (p + q) := (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e
  have hf : DifferentiableAt ℝ f y :=
    (Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart form.1.smooth e he hy).differentiableAt (by simp)
  have hpure := form.eventually_hasBidegree_inChart e he hy
  change (1 / 2 : ℂ) • (extDeriv f y + (DolbeaultProjection.dolbeaultPrimeCharacter p q)⁻¹ •
    Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E (p + q + 1) Complex.I (extDeriv f y)) = Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime f y
  rw [← Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_add_extDerivDoublePrime f y]
  apply DolbeaultProjection.dolbeaultPrimeProjection_of_characters
  · ext v
    exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_bidegree_character hf hpure DolbeaultProjection.dolbeaultIUnit v
  · ext v
    exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime_bidegree_character hf hpure DolbeaultProjection.dolbeaultIUnit v

/-- Every actual holomorphic chart identifies the global double-prime projection
with the ordinary local `d''` formula. -/
theorem manifoldDolbeaultDoublePrimeForm_eq_local (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    (DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)).inChart e y =
      Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e) y := by
  have h := congrArg (fun s : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 1) =>
    (s : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)).inChart e y)
      (DolbeaultProjection.manifoldDolbeaultPrimeForm_add_doublePrime E M p q form)
  change ((DolbeaultProjection.manifoldDolbeaultPrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)) +
    (DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1))).inChart e y =
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1 : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)).inChart e y at h
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add] at h
  change (DolbeaultProjection.manifoldDolbeaultPrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)).inChart e y +
    (DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)).inChart e y = _ at h
  rw [manifoldDolbeaultPrimeForm_eq_local form e he hy,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart form.1 e he hy] at h
  exact add_left_cancel (h.trans
    (Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_add_extDerivDoublePrime
      ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e) y).symm)

/-- The prime projection has the full raised geometric bidegree. -/
theorem manifoldDolbeaultPrimeForm_hasBidegree (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M (p + 1) q
      (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree (by omega : p + q + 1 = (p + 1) + q)
        (DolbeaultProjection.manifoldDolbeaultPrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1))) := by
  apply (DolbeaultCharacters.hasManifoldBidegree_castDegree_iff _ _).mpr
  intro e he y hy z v
  rw [manifoldDolbeaultPrimeForm_eq_local form e he hy]
  exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime_bidegree_character
    ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart form.1.smooth e he hy).differentiableAt (by simp))
    (form.eventually_hasBidegree_inChart e he hy) z v

/-- The double-prime projection has the full raised geometric bidegree. -/
theorem manifoldDolbeaultDoublePrimeForm_hasBidegree (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p (q + 1)
      (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.castDegree (by omega : p + q + 1 = p + (q + 1))
        (DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1))) := by
  apply (DolbeaultCharacters.hasManifoldBidegree_castDegree_iff _ _).mpr
  intro e he y hy z v
  rw [manifoldDolbeaultDoublePrimeForm_eq_local form e he hy]
  exact Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime_bidegree_character
    ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart form.1.smooth e he hy).differentiableAt (by simp))
    (form.eventually_hasBidegree_inChart e he hy) z v

end

namespace PureManifoldForm

/-- The genuine global `d'`, increasing the holomorphic degree. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M (p + 1) q :=
  (((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv
    (by omega : p + q + 1 = (p + 1) + q)).toLinearMap).comp
      (DolbeaultProjection.manifoldDolbeaultPrimeForm E M p q)).codRestrict _ (by
        intro form
        change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M (p + 1) q
          ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv
            (by omega : p + q + 1 = (p + 1) + q)
              (DolbeaultProjection.manifoldDolbeaultPrimeForm E M p q form) :
                Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M ((p + 1) + q)) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M ((p + 1) + q))
        rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv_apply, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_coe]
        exact manifoldDolbeaultPrimeForm_hasBidegree form)

/-- The genuine global `d''`, increasing the antiholomorphic degree. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p (q + 1) :=
  (((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv
    (by omega : p + q + 1 = p + (q + 1))).toLinearMap).comp
      (DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q)).codRestrict _ (by
        intro form
        change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p (q + 1)
          ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv
            (by omega : p + q + 1 = p + (q + 1))
              (DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q form) :
                Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + (q + 1))) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + (q + 1)))
        rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv_apply, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_coe]
        exact manifoldDolbeaultDoublePrimeForm_hasBidegree form)

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_coe (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M ((p + 1) + q)) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : p + q + 1 = (p + 1) + q)
        (DolbeaultProjection.manifoldDolbeaultPrimeForm E M p q form) :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegreeLinearEquiv_apply _ _

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + (q + 1))) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : p + q + 1 = p + (q + 1))
        (DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M p q form) := rfl

/-- The two genuine bidegree operators sum to the original exterior derivative. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : (p + 1) + q = p + q + 1) (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form).1 +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : p + (q + 1) = p + q + 1) (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form).1 =
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1 := by
  simpa only [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_coe, Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_castDegree,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self] using
      DolbeaultProjection.manifoldDolbeaultPrimeForm_add_doublePrime E M p q form

/-- The literal composite appearing in Clay's denominator. -/
def _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M (p + 1) (q + 1) :=
  Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime.comp Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime

@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime_apply (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime form = Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form) := rfl

end PureManifoldForm

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeault
