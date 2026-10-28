import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceProjectivePairing

/-! # Surface Topology Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceTopologyTransport.CM

noncomputable section

/-! ThetaCycle: transport the actual smooth topology along the proved surface
dimension equality, on the same underlying analytic manifold. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℂ) M]

theorem complex_surface_forms_tendsto (hd : d = 2) (n : ℕ)
    {I : Type*} (l : Filter I) (f : I → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℂ) M n)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℂ) M n)
    (h : let _ := SmoothTopology.CM.smoothFormTopology (Fin d → ℂ) M n
      Tendsto f l (𝓝 a)) :
    let _ := SurfaceProjectivePairing.CM.complexSurfaceChartedSpace (M := M) hd
    let _ := SmoothTopology.CM.smoothFormTopology (Fin 2 → ℂ) M n
    Tendsto (fun i => SurfaceProjectivePairing.CM.complexSurfaceForms hd n (f i)) l
      (𝓝 (SurfaceProjectivePairing.CM.complexSurfaceForms hd n a)) := by
  subst d
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceTopologyTransport.CM
