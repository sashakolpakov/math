import OAI.Analysis.DifferentialForms.Manifold.CechDeRham

/-! # Connection Transgression -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction

noncomputable section

/-! The actual signed Čech–de Rham differential identifies curvature
with the defect of logarithmic changes of local connection forms. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (U : I → Opens M)

theorem manifoldCechTotalInclusion_d_apply (p q n : ℕ) (h : p + q = n)
    (a : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U q p) :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) U).d n (n + 1)
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U p q n h a) =
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U (p + 1) q (n + 1) (by omega) (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U q p a) +
        ((-1 : ℤ) ^ p) • Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U p (q + 1) (n + 1) (by omega)
          (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U q p a) :=
  ConcreteCategory.congr_hom (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion_d U p q n h) a

def connectionTotalPrimitive
    (a : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 1 0)
    (l : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 0 1) : (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) U).X 1 :=
  Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 0 1 1 rfl a - Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 1 0 1 rfl l

theorem connectionTotalPrimitive_d
    (a : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 1 0)
    (l : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 0 1) :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) U).d 1 2 (connectionTotalPrimitive U a l) =
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 0 2 2 rfl (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 1 0 a) -
        Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 2 0 2 rfl (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 0 1 l) +
        Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 1 1 2 rfl
          (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 1 0 a + Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l) := by
  rw [connectionTotalPrimitive, map_sub, manifoldCechTotalInclusion_d_apply,
    manifoldCechTotalInclusion_d_apply, map_add]
  simp only [pow_zero, pow_one, one_smul, neg_one_smul]
  abel

theorem connectionTotalPrimitive_d_of_transition
    (a : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 1 0)
    (l : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 0 1)
    (h : Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 1 0 a = -Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l) :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) U).d 1 2 (connectionTotalPrimitive U a l) =
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 0 2 2 rfl (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 1 0 a) -
        Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 2 0 2 rfl (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 0 1 l) := by
  have hz : (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 1 0 a + Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l :
      Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 1 1) = 0 :=
    (congrArg (fun t : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 1 1 =>
      t + Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l) h).trans (by
        funext t
        apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
        intro x
        ext v
        change -((Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l) t x v) +
          (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l) t x v = 0
        exact neg_add_cancel _)
  have hm : Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 1 1 2 rfl
      (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 1 0 a + Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l) = 0 :=
    (congrArg (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 1 1 2 rfl).hom hz).trans
      (map_zero (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 1 1 2 rfl).hom)
  rw [connectionTotalPrimitive_d, hm, add_zero]

theorem connection_curvature_total_boundary
    (curvature : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2)
    (a : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 1 0)
    (l : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U 0 1)
    (hcurv : Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 1 0 a = Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation U 2 curvature)
    (htrans : Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 1 0 a = -Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD U 0 1 l) :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) U).d 1 2 (connectionTotalPrimitive U a l) =
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) U).f 2 curvature -
        Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U 2 0 2 rfl (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta U 0 1 l) := by
  rw [connectionTotalPrimitive_d_of_transition U a l htrans, hcurv]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction
