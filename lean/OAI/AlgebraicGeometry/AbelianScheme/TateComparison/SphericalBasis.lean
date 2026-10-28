import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralTypeUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalSpan

/-! # Spherical Basis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SphericalBasis

noncomputable section

/-! The actual raw spherical operators are a rational basis. Its
coordinates are evaluations of the finite raw kernel at representatives. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

def sphericalCoefficient (t : Local.LocalType s) : HeckeKernel.Hecke s q →ₗ[ℚ] ℚ :=
  (Finsupp.lapply (QuotientGroup.mk (HeckeKernel.representative s q t)⁻¹)).comp (HeckeKernel.kernelLinear (HeckeKernel.integralLevel s q))

theorem sphericalCoefficient_basis (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (u v : Local.LocalType s) :
    sphericalCoefficient s q u (CentralConvolution.sphericalBasis s q v) = if v = u then 1 else 0 := by
  change HeckeKernel.kernel (HeckeKernel.integralLevel s q) (CentralConvolution.sphericalBasis s q v)
    (QuotientGroup.mk (HeckeKernel.representative s q u)⁻¹) = _
  rw [HeckeKernel.raw_kernel_at (HeckeKernel.integralLevel s q) (CentralConvolution.sphericalBasis_isRaw s q v)]
  have hu : QuotientGroup.mk (HeckeKernel.representative s q u)⁻¹ ∈
      HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q u) := ⟨1, one_smul _ _⟩
  have hi : QuotientGroup.mk (HeckeKernel.representative s q u)⁻¹ ∈
      HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q v) ↔ v = u := by
    constructor
    · intro hv
      exact IntegralTypeUniqueness.rawType_eq_of_common s q hElementaryDivisors v u _ hv hu
    · rintro rfl
      exact hu
  rw [hi]

theorem sphericalCoefficient_expansion (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (c : Local.LocalType s →₀ ℚ) (t : Local.LocalType s) :
    sphericalCoefficient s q t (Finsupp.linearCombination ℚ (CentralConvolution.sphericalBasis s q) c) = c t := by
  change sphericalCoefficient s q t (c.sum (fun u r => r • CentralConvolution.sphericalBasis s q u)) = _
  rw [map_finsuppSum]
  simp only [map_smul, sphericalCoefficient_basis s q hElementaryDivisors, smul_eq_mul]
  simp_all

theorem linearIndependent_of_coefficient_recovery {I V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : I → V) (c : I → V →ₗ[ℚ] ℚ)
    (hc : ∀ l i, c i (Finsupp.linearCombination ℚ v l) = l i) : LinearIndependent ℚ v := by
  apply linearIndependent_iff.mpr
  intro l hl
  ext i
  have h := congrArg (c i) hl
  rw [hc, map_zero] at h
  exact h

theorem sphericalBasis_linearIndependent (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    LinearIndependent ℚ (CentralConvolution.sphericalBasis s q) := by
  exact linearIndependent_of_coefficient_recovery (CentralConvolution.sphericalBasis s q) (sphericalCoefficient s q)
    (sphericalCoefficient_expansion s q hElementaryDivisors)

def sphericalModuleBasis (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    Module.Basis (Local.LocalType s) ℚ (HeckeKernel.Hecke s q) :=
  Module.Basis.mk (sphericalBasis_linearIndependent s q hElementaryDivisors)
    (by rw [RationalSpan.sphericalBasis_span s q hElementaryDivisors])

theorem sphericalModuleBasis_apply (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (t : Local.LocalType s) :
    sphericalModuleBasis s q hElementaryDivisors t = CentralConvolution.sphericalBasis s q t := Module.Basis.mk_apply _ _ _

theorem sphericalModuleBasis_repr (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (T : HeckeKernel.Hecke s q) (t : Local.LocalType s) :
    (sphericalModuleBasis s q hElementaryDivisors).repr T t = sphericalCoefficient s q t T := by
  have h := sphericalCoefficient_expansion s q hElementaryDivisors ((sphericalModuleBasis s q hElementaryDivisors).repr T) t
  have hb : Finsupp.linearCombination ℚ (CentralConvolution.sphericalBasis s q)
      ((sphericalModuleBasis s q hElementaryDivisors).repr T) = T := by
    have he : (sphericalModuleBasis s q hElementaryDivisors : Local.LocalType s → HeckeKernel.Hecke s q) = CentralConvolution.sphericalBasis s q :=
      funext (sphericalModuleBasis_apply s q hElementaryDivisors)
    exact (congrArg (fun f : Local.LocalType s → HeckeKernel.Hecke s q => Finsupp.linearCombination ℚ f
      ((sphericalModuleBasis s q hElementaryDivisors).repr T)) he).symm.trans
      ((sphericalModuleBasis s q hElementaryDivisors).linearCombination_repr T)
  rw [hb] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SphericalBasis
