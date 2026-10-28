import OAI.AlgebraicGeometry.Comparison.Betti.AdaptedHolomorphicGermSlice
import OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticInverse

/-! # Normal Equation Kernel -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.NormalEquationKernel.AnalyticLocal

noncomputable section

/-! Independent normal equations in a holomorphic coordinate system generate the original local restriction kernel. -/

open Set Filter
open scoped _root_.Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}

def normalEquationGerm (q : F → E × (Fin n → ℂ)) (y : F) (hq : ContDiffAt ℂ ω q y) (i : Fin n) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y :=
  LocalHolomorphicComposition.Analytic.localHolomorphicComposition q y hq (Finite.NormalSlice.AnalyticLocal.normalCoordinateGerm (q y).1 (q y).2 i)

theorem normalEquationGerm_val (q : F → E × (Fin n → ℂ)) (y : F) (hq : ContDiffAt ℂ ω q y) (i : Fin n) :
    (normalEquationGerm q y hq i).val =
      ((fun p : F => (q p).2 i - (q y).2 i) : Germ (𝓝 y) ℂ) := rfl

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem holomorphicNormalEquation_kernel_le
    (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x) (y : F) (hfy : f x = y)
    (q : F → E × (Fin n → ℂ)) (hq : ContDiffAt ℂ ω q y)
    (hbij : Function.Bijective (fderiv ℂ q y))
    (z : Fin n → ℂ) (hcoords : (fun u => q (f u)) =ᶠ[𝓝 x] (fun u => (u, z)))
    (J : Ideal (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y)) (hJ : ∀ i, normalEquationGerm q y hq i ∈ J) :
    RingHom.ker (LocalHolomorphicComposition.Analytic.localHolomorphicCompositionAt f x hf y hfy) ≤ J := by
  obtain ⟨e, hy, heq, he, hi⟩ := Cycles.Functoriality.AnalyticInverse.Construction.exists_analytic_localInverse q y hq hbij
  have hqy : q y = (x, z) := by
    rw [← hfy]
    exact hcoords.eq_of_nhds
  have hey : e y = (x, z) := (congrFun heq y).trans hqy
  have hecoords : (fun u => e (f u)) =ᶠ[𝓝 x] (fun u => (u, z)) := by
    simpa only [heq] using hcoords
  have hnormal (i : Fin n) :
      AdaptedHolomorphicGermSlice.AnalyticLocal.adaptedNormalCoordinateGerm e (he.differentiableOn (by simp)) y hy z i = normalEquationGerm q y hq i := by
    apply Subtype.ext
    rw [normalEquationGerm_val]
    change ((fun p : F => (e p).2 i - z i) : Germ (𝓝 y) ℂ) =
      ((fun p : F => (q p).2 i - (q y).2 i) : Germ (𝓝 y) ℂ)
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun p => by rw [heq, hqy])
  exact AdaptedHolomorphicGermSlice.AnalyticLocal.adaptedHolomorphicGermSlice_kernel_le f x hf y hfy e
    (he.differentiableOn (by simp)) (hi.differentiableOn (by simp)) hy z hey hecoords J
      (fun i => (hnormal i).symm ▸ hJ i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.NormalEquationKernel.AnalyticLocal
