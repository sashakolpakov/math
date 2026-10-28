import OAI.AlgebraicGeometry.CycleClass.Thom.VectorSubmersionCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable

/-! # Equation Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EquationNormalPair.Constructions

noncomputable section

/-! A submersion whose actual zero locus is the embedded support gives
normal pairs for that support, inside any prescribed open neighborhood.
Only the equations and their differential enter the construction. -/

open scoped ContDiff _root_.Topology _root_.Manifold
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable

open OAI.AlgebraicGeometry.CycleClass.Thom.VectorSubmersionCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions

variable {M N E F D G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]

theorem exists_equation_normalPair (u : M → N) (x : M)
    (c : OpenPartialHomeomorph N E) (hc : c.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E))
    (U : Set N) (hU : IsOpen U) (hxU : u x ∈ U) (hUc : U ⊆ c.source)
    (f : E → F) (hf : ContDiffAt ℂ ω f (c (u x)))
    (hs : Function.Surjective (fderiv ℂ f (c (u x))))
    (hzero : ∀ y ∈ U, y ∈ Set.range u ↔ f (c y) = 0)
    (e : (fderiv ℂ f (c (u x))).ker ≃L[ℂ] D) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D F u x,
      P.neighborhood ⊆ U ∧
      P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, D × F) ∧
      ∀ y : P.neighborhood, P.normalCoordinate y = f (c y.val) := by
  obtain ⟨q, hxq, hqx, hq, hqf, hqi⟩ :=
    VectorSubmersionCoordinates.Constructions.exists_analytic_submersion_coordinates f (c (u x)) hf hs
  let K := (fderiv ℂ f (c (u x))).ker
  let k : (F × K) ≃L[ℂ] (D × F) :=
    (LinearIsometryEquiv.prodComm ℂ F K).toContinuousLinearEquiv.trans
      (e.prodCongr (ContinuousLinearEquiv.refl ℂ F))
  let r := (c.trans q).transHomeomorph k.toHomeomorph
  have hrx : r (u x) = (0, 0) := by
    change k (q (c (u x))) = 0
    rw [hqx, (hzero (u x) hxU).mp ⟨x, rfl⟩]
    exact map_zero k
  have hx : u x ∈ r.source := ⟨hUc hxU, hxq⟩
  have hqd : q.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F × K) :=
    ⟨hqf.contMDiffOn.mdifferentiableOn (by simp),
      hqi.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hrd : r.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, D × F) := by
    change ((c.trans q).transHomeomorph k.toHomeomorph).MDifferentiable _ _
    rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
    exact (hc.trans hqd).trans
      ⟨(k.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn,
        (k.symm.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn⟩
  obtain ⟨s, hs, hst, hsub⟩ := Product.NormalPair.Constructions.centeredChart_exists_radius r hx hrx hU hxU
  let P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D F u x := {
    radius := s
    radius_pos := hs
    ambientChart := r
    product_subset_target := hst
    point_mem_source := hx
    point_coordinates := hrx
    range_iff := fun y hy => by
      change y ∈ Set.range u ↔ (q (c y)).1 = 0
      rw [hq]
      exact hzero y (hsub hy) }
  exact ⟨P, hsub, hrd, fun y => hq (c y.val)⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EquationNormalPair.Constructions
