import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Support -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Support

noncomputable section

/-! The inverse-representative support of convolution stays in any
submonoid. This controls the integral range independently of coefficients. -/

open scoped Classical

variable {G : Type*} [Group G] (U : Subgroup G) (M : Submonoid G)

def KernelSupportedIn (T : HeckeKernel.SphericalHecke U) : Prop :=
  ∀ g : G, HeckeKernel.kernel U T (QuotientGroup.mk g) ≠ 0 → g⁻¹ ∈ M

theorem kernelSupportedIn_mul (S T : HeckeKernel.SphericalHecke U)
    (hS : KernelSupportedIn U M S) (hT : KernelSupportedIn U M T) :
    KernelSupportedIn U M (S * T) := by
  intro x hx
  have hSmap : S.val = HeckeKernel.kernelOperator U (HeckeKernel.kernel U S) (HeckeKernel.kernel_invariant U S) :=
    (congrArg Subtype.val (HeckeKernel.heckeOfKernel_kernel U S)).symm
  rw [HeckeKernel.kernel_mul, hSmap, HeckeKernel.kernelOperator_apply] at hx
  obtain ⟨y, hy, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  revert hy hxy
  induction y using Quotient.inductionOn with
  | h y =>
    intro hy hxy
    have hcol := (mul_ne_zero_iff.mp hxy).2
    rw [HeckeKernel.kernelColumn_mk, CentralConvolution.translate_apply] at hcol
    have hs := hS (y⁻¹ * x) hcol
    have ht := hT y (Finsupp.mem_support_iff.mp hy)
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] using M.mul_mem hs ht

theorem kernelSupportedIn_raw (hlevel : ∀ g ∈ U, g ∈ M) {g : G} {T : HeckeKernel.SphericalHecke U}
    (hg : g ∈ M) (hT : HeckeKernel.IsRawDoubleCoset U g T) : KernelSupportedIn U M T := by
  intro x hx
  have hm : QuotientGroup.mk x ∈ HeckeKernel.doubleCosetOrbit U g := by
    by_contra hnot
    rw [HeckeKernel.raw_kernel_at U hT, ite_eq_right hnot] at hx
    exact hx rfl
  obtain ⟨k, l, rfl⟩ := (HeckeKernel.mem_doubleCosetOrbit U g x).mp hm
  rw [mul_inv_rev, mul_inv_rev, inv_inv]
  exact M.mul_mem (hlevel _ (U.inv_mem l.property))
    (M.mul_mem hg (hlevel _ (U.inv_mem k.property)))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Support
