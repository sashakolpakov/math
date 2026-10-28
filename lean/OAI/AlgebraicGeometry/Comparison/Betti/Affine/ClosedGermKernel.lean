import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedNormalCoordinates
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedGermQuotient
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.NormalEquationKernel

/-! # Closed Germ Kernel -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedGermKernel.AnalyticLocal

noncomputable section

section

/-! The actual holomorphic restriction kernel is the extension of the original algebraic defining ideal. -/

open scoped ContDiff _root_.Topology

open Filter

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  [IsDomain B] [Algebra.Smooth ℂ B] {m : ℕ}
  (h : A →ₐ[ℂ] B) (hh : Function.Surjective h)
  (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
    (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
  (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
  (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B))
  (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
  (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source)

include hh

theorem affineChartGermPullback_ker_le_originalIdeal :
    RingHom.ker (ClosedGermQuotient.AnalyticLocal.affineChartGermPullback h e f he hf x hx hfx) ≤
      ClosedGermQuotient.AnalyticLocal.affineClosedGermIdeal h f hf x hfx := by
  obtain ⟨k, a, Ψ, hq, hbij, hcoords⟩ :=
    ClosedNormalCoordinates.affineClosed_exists_normalCoordinates h hh e f he hf x hx hfx
  let q := fun w => (Ψ w, fun i => f.symm w (a i))
  have hnormal (i : Fin k) : Holomorphic.NormalEquationKernel.AnalyticLocal.normalEquationGerm q (f (x.comp h)) hq i =
      ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx (a i) := by
    apply Subtype.ext
    rw [Holomorphic.NormalEquationKernel.AnalyticLocal.normalEquationGerm_val, ChartGermMap.AnalyticLocal.affineChartGermMap_val]
    apply Germ.coe_eq.mpr
    apply Eventually.of_forall
    intro w
    change f.symm w (a i) - f.symm (f (x.comp h)) (a i) = f.symm w (a i)
    rw [f.left_inv hfx]
    change f.symm w (a i) - x (h (a i)) = f.symm w (a i)
    have hai : h (a i) = 0 := (a i).property
    rw [hai, map_zero, sub_zero]
  apply Holomorphic.NormalEquationKernel.AnalyticLocal.holomorphicNormalEquation_kernel_le
    (fun z => f ((e.symm z).comp h)) (e x)
    (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx) (f (x.comp h))
    (by rw [e.left_inv hx]) q hq hbij 0 hcoords
  intro i
  rw [hnormal]
  exact Ideal.mem_map_of_mem (ChartGermMap.AnalyticLocal.affineChartGermMap f hf (x.comp h) hfx) (a i).property

theorem affineChartGermPullback_ker :
    RingHom.ker (ClosedGermQuotient.AnalyticLocal.affineChartGermPullback h e f he hf x hx hfx) =
      ClosedGermQuotient.AnalyticLocal.affineClosedGermIdeal h f hf x hfx :=
  le_antisymm (affineChartGermPullback_ker_le_originalIdeal h hh e f he hf x hx hfx)
    (ClosedGermQuotient.AnalyticLocal.affineClosedGermIdeal_le_ker h e f he hf x hx hfx)

theorem affineClosedGermQuotientMap_bijective :
    Function.Bijective (ClosedGermQuotient.AnalyticLocal.affineClosedGermQuotientMap h e f he hf x hx hfx) := by
  constructor
  · exact RingHom.lift_injective_of_ker_le_ideal _
      (ClosedGermQuotient.AnalyticLocal.affineClosedGermIdeal_le_ker h e f he hf x hx hfx)
      (affineChartGermPullback_ker_le_originalIdeal h hh e f he hf x hx hfx)
  · exact ClosedGermQuotient.AnalyticLocal.affineClosedGermQuotientMap_surjective h e f he hf x hx hfx hh

end

/-! The exact affine germ kernel theorem in any regular chart of the proved native dimension. -/

theorem affineChartGermPullback_ker_of_dimension
    {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    [IsDomain B] [Algebra.Smooth ℂ B] {n m : ℕ}
    (hn : Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B = n)
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source) :
    RingHom.ker (ClosedGermQuotient.AnalyticLocal.affineChartGermPullback h e f he hf x hx hfx) =
      ClosedGermQuotient.AnalyticLocal.affineClosedGermIdeal h f hf x hfx := by
  subst n
  exact affineChartGermPullback_ker h hh e f he hf x hx hfx

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedGermKernel.AnalyticLocal
