import OAI.LinearAlgebra.Moore.Rank.Mixed.Definition
import OAI.LinearAlgebra.Moore.Boundary

noncomputable section
namespace OAI.LinearAlgebra.Moore

open Matrix
open scoped Matrix.Norms.Elementwise

theorem continuous_mooreMultilinear (n : ℕ) : Continuous (mooreMultilinear n) := by
  change Continuous (fun A => mooreMultilinear n A)
  simp only [mooreMultilinear_apply]
  apply Complex.continuous_re.comp
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  exact (continuous_skewComplexify_entry (σ (i, 0)) (σ (i, 1))).comp (continuous_apply i)

theorem continuous_mixedMoore (n : ℕ) : Continuous (mixedMoore n) := by
  change Continuous (fun A => mixedMoore n A)
  simp only [mixedMoore_apply]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ _
  exact (continuous_mooreMultilinear n).comp (continuous_pi (fun i => continuous_apply (σ i)))

end OAI.LinearAlgebra.Moore
