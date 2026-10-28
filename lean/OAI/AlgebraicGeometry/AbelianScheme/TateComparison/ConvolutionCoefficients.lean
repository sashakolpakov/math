import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralCartan
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Support

/-! # Convolution Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionCoefficients

noncomputable section

/-! Natural convolution multiplicities constructed from actual raw
double cosets and ElementaryDivisors. No convolution identity is an input. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

theorem sphericalBasis_integral_support (t : Local.IntegralType s) :
    Support.KernelSupportedIn (HeckeKernel.integralLevel s q) (IntegralCartan.integralSplitMonoid s q)
      (CentralConvolution.sphericalBasis s q t.val) :=
  Support.kernelSupportedIn_raw _ _ (fun _ hg => IntegralCartan.level_mem_integralSplitMonoid s q hg)
    (IntegralCartan.representative_mem_integralSplitMonoid s q t) (CentralConvolution.sphericalBasis_isRaw s q t.val)

theorem integral_support_covered (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (T : HeckeKernel.Hecke s q) (hT : Support.KernelSupportedIn (HeckeKernel.integralLevel s q) (IntegralCartan.integralSplitMonoid s q) T) :
    ∀ x ∈ (HeckeKernel.kernel (HeckeKernel.integralLevel s q) T).support,
      ∃ t : Local.IntegralType s, x ∈ HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t.val) := by
  intro x
  induction x using Quotient.inductionOn with
  | h x =>
    intro hx
    obtain ⟨t, l, r, hxr⟩ := IntegralCartan.exists_integral_split_cartan s q hElementaryDivisors x⁻¹
      (hT x (Finsupp.mem_support_iff.mp hx))
    refine ⟨t, (HeckeKernel.mem_doubleCosetOrbit _ _ _).mpr ⟨r⁻¹, l⁻¹, ?_⟩⟩
    have h := congrArg Inv.inv hxr
    simpa only [inv_inv, mul_inv_rev, Subgroup.coe_inv, mul_assoc] using h

/-- Raw convolution of two integral types has finitely supported natural
multiplicities, all still in the integral range. -/
theorem exists_spherical_convolution (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v : Local.IntegralType s) :
    ∃ c : Local.IntegralType s →₀ ℕ,
      CentralConvolution.sphericalBasis s q u.val * CentralConvolution.sphericalBasis s q v.val =
        c.sum (fun w n => n • CentralConvolution.sphericalBasis s q w.val) := by
  apply HeckeKernel.exists_raw_expansion (HeckeKernel.integralLevel s q)
    (fun t : Local.IntegralType s => HeckeKernel.representative s q t.val)
    (fun t : Local.IntegralType s => CentralConvolution.sphericalBasis s q t.val)
    (fun t => CentralConvolution.sphericalBasis_isRaw s q t.val)
  · exact HeckeKernel.natValued_kernel_mul _ _ _
      (HeckeKernel.raw_natValued _ (CentralConvolution.sphericalBasis_isRaw s q u.val))
      (HeckeKernel.raw_natValued _ (CentralConvolution.sphericalBasis_isRaw s q v.val))
  · apply integral_support_covered s q hElementaryDivisors
    exact Support.kernelSupportedIn_mul _ _ _ _
      (sphericalBasis_integral_support s q u) (sphericalBasis_integral_support s q v)

def convolutionCoefficients (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v : Local.IntegralType s) : Local.IntegralType s →₀ ℕ :=
  (exists_spherical_convolution s q hElementaryDivisors u v).choose

theorem spherical_convolution (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (u v : Local.IntegralType s) :
    CentralConvolution.sphericalBasis s q u.val * CentralConvolution.sphericalBasis s q v.val =
      (convolutionCoefficients s q hElementaryDivisors u v).sum (fun w n => n • CentralConvolution.sphericalBasis s q w.val) :=
  (exists_spherical_convolution s q hElementaryDivisors u v).choose_spec

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionCoefficients
