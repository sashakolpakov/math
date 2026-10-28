import Mathlib

/-! # Partial Smooth Jets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PartialSmoothJets.CM

noncomputable section

/-! ThetaCycle: partial derivatives of a smooth parameter family remain smooth,
for the real derivatives defining the actual C-infinity topology. -/

open scoped ContDiff

theorem partial_iteratedFDeriv_smoothAt
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F → G} {x : E} {z : F}
    (h : ContDiffAt 𝕜 ∞ (Function.uncurry f) (x, z)) (a : ℕ) :
    ContDiffAt 𝕜 ∞ (fun w : E × F => iteratedFDeriv 𝕜 a (f w.1) w.2) (x, z) := by
  induction a with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using!
      h.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 𝕜 F G).symm : G →L[𝕜] F [×0]→L[𝕜] G)
  | succ a ih =>
    have hc : ContDiffAt 𝕜 ∞
        (fun w : (E × F) × F => iteratedFDeriv 𝕜 a (f w.1.1) w.2) ((x, z), z) :=
      ih.comp ((x, z), z) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt 𝕜 ∞
        (fun w : E × F => fderiv 𝕜 (iteratedFDeriv 𝕜 a (f w.1)) w.2) (x, z) :=
      hc.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Function.uncurry_def] using!
      hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (a + 1) => F) G).symm :
          (F →L[𝕜] F [×a]→L[𝕜] G) →L[𝕜] F [×(a + 1)]→L[𝕜] G)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PartialSmoothJets.CM
