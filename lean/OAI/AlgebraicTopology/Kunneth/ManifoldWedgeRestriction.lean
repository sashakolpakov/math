import OAI.AlgebraicTopology.Kunneth.SimplexWedgeIntegral
import OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge

/-! # Manifold Wedge Restriction -/

namespace OAI.AlgebraicTopology.Kunneth.ManifoldWedgeRestriction

noncomputable section

/-! Restriction of actual manifold exterior products to the simplex tensor model. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial TensorProduct

namespace Constructions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {p q : ℕ}

local instance wedgeRestrictionFormsAddGroup (n : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm V n) := inferInstance
local instance wedgeRestrictionFormsModule (n : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm V n) := inferInstance
local instance wedgeRestrictionTangentNormedGroup (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance wedgeRestrictionTangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

theorem parameterFormPullback_wedge (f : V → M) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    SimplexFormPullback.Constructions.parameterFormPullback f hf (ManifoldWedge.Constructions.manifoldWedge a b) =
      WedgeAlgebra.Constructions.normedWedge (SimplexFormPullback.Constructions.parameterFormPullback f hf a) (SimplexFormPullback.Constructions.parameterFormPullback f hf b) := by
  apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext
  intro x
  exact (CovectorWedge.Constructions.covectorWedge_pullback
    ((mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f x).comp
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.toContinuousLinearMap)
    (a (f x)) (b (f x))).symm

theorem simplexManifoldFormRestriction_wedge {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma (p + q) (ManifoldWedge.Constructions.manifoldWedge a b) =
      RestrictedWedge.Constructions.restrictedWedge (SimplexFormDomain.Constructions.coordinateSimplex n) p q
        (SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a) (SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma q b) := by
  change RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex n) (p + q)
    (SimplexFormPullback.Constructions.parameterFormPullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma) _ (ManifoldWedge.Constructions.manifoldWedge a b)) =
      RestrictedForms.Constructions.restrictForm (SimplexFormDomain.Constructions.coordinateSimplex n) (p + q)
        (WedgeAlgebra.Constructions.normedWedge (SimplexFormPullback.Constructions.parameterFormPullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma) _ a)
          (SimplexFormPullback.Constructions.parameterFormPullback (SimplexFormExtension.Constructions.globalSimplexParameter sigma) _ b))
  rw [parameterFormPullback_wedge]

theorem simplexManifoldFormRestriction_cast {n k l : ℕ} (h : k = l)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma l (ManifoldWedge.Constructions.manifoldDegreeCast h a) =
      RestrictedWedge.Constructions.restrictedFormDegreeCast (SimplexFormDomain.Constructions.coordinateSimplex n) h (SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma k a) := by
  subst l
  rfl

def simplexManifoldClosedRestriction {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) : SimplicialForms.Constructions.SimplexClosedForms n q :=
  ⟨SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma q b.val, by
    change RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) q
      (SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma q b.val) = 0
    rw [SimplexFormPullback.Constructions.simplexManifoldFormRestriction_d, b.property, map_zero]⟩

def simplexManifoldTensorRestriction {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) : TensorSimplicialForms.Constructions.SimplexFormTensor q n p :=
  SimplexFormPullback.Constructions.simplexManifoldFormRestriction sigma p a ⊗ₜ[ℂ] simplexManifoldClosedRestriction sigma b

theorem simplexManifoldTensorRestriction_d {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    TensorSimplicialForms.Constructions.simplexFormTensorD q n p (simplexManifoldTensorRestriction sigma a b) =
      simplexManifoldTensorRestriction sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) b := by
  unfold simplexManifoldTensorRestriction
  rw [TensorSimplicialForms.Constructions.simplexFormTensorD_tmul, SimplexFormPullback.Constructions.simplexManifoldFormRestriction_d]

theorem simplexManifoldTensorRestriction_closed {n : ℕ}
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    TensorSimplicialForms.Constructions.simplexFormTensorD q n p (simplexManifoldTensorRestriction sigma a.val b) = 0 := by
  rw [simplexManifoldTensorRestriction_d, a.property]
  unfold simplexManifoldTensorRestriction
  rw [map_zero, TensorProduct.zero_tmul]

theorem simplexManifoldTensorRestriction_face {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    simplexManifoldTensorRestriction
      ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet.map f.op sigma) a b =
      TensorSimplicialForms.Constructions.simplexFormTensorPullback f q p (simplexManifoldTensorRestriction sigma a b) := by
  unfold simplexManifoldTensorRestriction TensorSimplicialForms.Constructions.simplexFormTensorPullback
  rw [TensorProduct.map_tmul, SimplexFormPullback.Constructions.simplexManifoldFormRestriction_face]
  congr 1
  apply Subtype.ext
  exact SimplexFormPullback.Constructions.simplexManifoldFormRestriction_face f sigma b.val

theorem simplexWedgeIntegral_manifold (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋q + p⦌) :
    SimplexWedgeIntegral.Constructions.simplexWedgeIntegral q p (simplexManifoldTensorRestriction sigma a b) =
      DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration sigma
        (ManifoldWedge.Constructions.manifoldDegreeCast (Nat.add_comm p q) (ManifoldWedge.Constructions.manifoldWedge a b.val)) := by
  rw [← RestrictedSimplexIntegration.Constructions.simplexIntegral_manifoldRestriction, simplexManifoldFormRestriction_cast,
    simplexManifoldFormRestriction_wedge]
  rfl

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.ManifoldWedgeRestriction
