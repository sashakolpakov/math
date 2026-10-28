import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion
import OAI.Analysis.Normed.Function.Holder.C2HolderExt

open Set
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

/-- The boundary Hessian stored in the genuine C²,α space is Hermitian as
well: it is the continuous limit of the actual interior Hessian. -/
theorem quaternionHessianField_isHermitian {n s : ℕ}
    {Ω K : Set (CoordinateSpace n s)} {hΩK : Ω ⊆ K} {α : ℝ}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω) (e : Fin s → Q)
    (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (x : K) :
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α e f) x).IsHermitian := by
  let a := OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α e f)
  have hc := OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension a
  have hstar : Continuous (fun A : Matrix (Fin n) (Fin n) Q ↦ Aᴴ) := by fun_prop
  have hi : EqOn (fun y ↦ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension a y)ᴴ) (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension a) Ω := by
    intro y hy
    change (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension a y)ᴴ = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension a y
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply a (hΩK hy)]
    have hH := quaternionHessian_isHermitian e
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ f).contDiffAt (hΩ.mem_nhds hy))
    simpa only [a, quaternionHessianField_eq hΩ hΩK α e f hy, Matrix.IsHermitian] using hH
  have hk := hi.of_subset_closure (hstar.comp_continuousOn hc) hc hΩK hKΩ
  change (a x)ᴴ = a x
  simpa only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply a x.property] using hk x.property

end OAI.Analysis.PDE.Dirichlet
