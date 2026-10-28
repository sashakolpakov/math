import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback

/-! # Projective Pure Pullback -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectivePurePullback.IntegralProjectiveVariety

noncomputable section

/-!
# Algebraic pullback preserves actual pure de Rham classes

An actual morphism over the complex base is complex smooth on the proved
native analytic manifolds. Its pullback therefore preserves the literal
complex tangent-type condition on closed forms. The existing de Rham class
map then proves preservation of the actual pure de Rham subspaces.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- Algebraic pullback preserves the actual inverse-character tangent-type
condition of a closed form. Analytic smoothness is derived from the algebraic
morphism and is not an extra hypothesis. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.closedFormPullback_hasTangentBidegree (φ : V.toOver ⟶ W.toOver) (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms W.analyticModel W.analyticSpace (p + q))
    (hform : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree W.analyticModel W.analyticSpace p q
      (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm W.analyticModel W.analyticSpace (p + q))) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree V.analyticModel V.analyticSpace p q
      ((Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
          (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞) (p + q) form).val :
        Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace (p + q)) := by
  apply (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp
  exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.pullback
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr hform)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complex_contMDiff_map φ ∞)

/-- Pulling back the actual class of a closed form gives the class of its
actual pullback. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_closedFormClass (φ : V.toOver ⟶ W.toOver) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms W.analyticModel W.analyticSpace n) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ n (W.deRhamClass n form) =
      V.deRhamClass n (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
        (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞) n form) :=
  Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞) n form

/-- The pullback of a class admitting a genuine closed pure representative
again admits such a representative of the same bidegree. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_mem_pureDeRhamSubspace (φ : V.toOver ⟶ W.toOver) (p q : ℕ)
    {a : W.deRhamCohomology (p + q)} (ha : a ∈ W.pureDeRhamSubspace p q) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ (p + q) a ∈ V.pureDeRhamSubspace p q := by
  obtain ⟨form, hform, rfl⟩ := (W.mem_pureDeRhamSubspace_iff p q a).mp ha
  apply (V.mem_pureDeRhamSubspace_iff p q _).mpr
  refine ⟨Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ)
      (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map φ ∞) (p + q) form,
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.closedFormPullback_hasTangentBidegree φ p q form hform, ?_⟩
  exact (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_closedFormClass φ (p + q) form).symm

/-- Algebraic pullback sends the pure de Rham subspace into the corresponding
actual pure subspace on the source variety. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.pureDeRhamSubspace_map_pullback_le (φ : V.toOver ⟶ W.toOver) (p q : ℕ) :
    (W.pureDeRhamSubspace p q).map (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ (p + q)).hom ≤
      V.pureDeRhamSubspace p q := by
  rintro _ ⟨a, ha, rfl⟩
  exact AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_mem_pureDeRhamSubspace φ p q ha

/-- Restriction of the existing algebraic de Rham pullback to the actual
pure-class subspaces. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.pureDeRhamPullback (φ : V.toOver ⟶ W.toOver) (p q : ℕ) :
    W.pureDeRhamSubspace p q →ₗ[ℂ] V.pureDeRhamSubspace p q where
  toFun a := ⟨AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ (p + q) a.val,
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_mem_pureDeRhamSubspace φ p q a.property⟩
  map_add' a b := Subtype.ext ((AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ (p + q)).hom.map_add a.val b.val)
  map_smul' c a := Subtype.ext ((AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ (p + q)).hom.map_smul c a.val)

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.pureDeRhamPullback_coe (φ : V.toOver ⟶ W.toOver) (p q : ℕ)
    (a : W.pureDeRhamSubspace p q) :
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.pureDeRhamPullback φ p q a : V.deRhamCohomology (p + q)) =
      AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback φ (p + q) a.val := rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectivePurePullback.IntegralProjectiveVariety
