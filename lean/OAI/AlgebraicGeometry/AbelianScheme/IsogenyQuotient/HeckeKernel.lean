import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Hecke Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HeckeKernel.Construction

noncomputable section

/-!
Construct actual spherical convolution operators from finite invariant
kernels. This supplies existence in the raw Hecke model used by TateComparison,
without assuming an operator with the desired action already exists.
-/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

variable {G : Type*} [Group G] (U : Subgroup G)

/-- A finite identity column invariant under the integral level determines
the column at every right coset, independently of its representative. -/
def invariantKernelColumn (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) : G ⧸ U → TateComparison.HeckeKernel.CosetModule U :=
  Quotient.lift (fun g => TateComparison.HeckeKernel.translate U g k) (by
    intro x y hxy
    let u : U := ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.mp hxy⟩
    have hy : y = x * (u : G) := by simp [u]
    rw [hy, TateComparison.HeckeKernel.translate_mul, Module.End.mul_apply, hk])

@[simp]
theorem invariantKernelColumn_mk (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) (g : G) :
    invariantKernelColumn U k hk (QuotientGroup.mk g) = TateComparison.HeckeKernel.translate U g k := rfl

theorem invariantKernelColumn_smul (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) (g : G) (x : G ⧸ U) :
    invariantKernelColumn U k hk (g • x) = TateComparison.HeckeKernel.translate U g (invariantKernelColumn U k hk x) := by
  induction x using Quotient.inductionOn with
  | h x =>
    change TateComparison.HeckeKernel.translate U (g * x) k = TateComparison.HeckeKernel.translate U g (TateComparison.HeckeKernel.translate U x k)
    rw [TateComparison.HeckeKernel.translate_mul, Module.End.mul_apply]

/-- Linear extension of the prescribed columns. -/
def invariantKernelOperator (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) : Module.End ℚ (TateComparison.HeckeKernel.CosetModule U) :=
  Finsupp.linearCombination ℚ (invariantKernelColumn U k hk)

@[simp]
theorem invariantKernelOperator_single (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) (x : G ⧸ U) (r : ℚ) :
    invariantKernelOperator U k hk (Finsupp.single x r) = r • invariantKernelColumn U k hk x :=
  Finsupp.linearCombination_single ℚ r x

/-- The constructed operator commutes with the entire group action and
therefore belongs to the actual spherical Hecke algebra. -/
def sphericalHeckeFromKernel (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) : TateComparison.HeckeKernel.SphericalHecke U := by
  refine ⟨invariantKernelOperator U k hk, ?_⟩
  rintro t ⟨g, rfl⟩
  apply Finsupp.lhom_ext
  intro x r
  simp only [Module.End.mul_apply, invariantKernelOperator_single, TateComparison.HeckeKernel.translate_single,
    map_smul, invariantKernelColumn_smul]

/-- Its identity column is the supplied kernel, with coefficient one
unchanged; this is the raw, integral-level-volume-one convention. -/
theorem sphericalHeckeFromKernel_kernel (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) :
    TateComparison.HeckeKernel.kernel U (sphericalHeckeFromKernel U k hk) = k := by
  change invariantKernelOperator U k hk (Finsupp.single (QuotientGroup.mk (1 : G)) 1) = k
  rw [invariantKernelOperator_single, one_smul, invariantKernelColumn_mk, TateComparison.HeckeKernel.translate_one]
  rfl

/-- Invariant finite kernels determine unique actual Hecke operators. -/
theorem exists_unique_spherical_hecke_with_kernel (k : TateComparison.HeckeKernel.CosetModule U)
    (hk : ∀ u : U, TateComparison.HeckeKernel.translate U (u : G) k = k) :
    ∃! T : TateComparison.HeckeKernel.SphericalHecke U, TateComparison.HeckeKernel.kernel U T = k := by
  refine ⟨sphericalHeckeFromKernel U k hk, sphericalHeckeFromKernel_kernel U k hk, ?_⟩
  intro T hT
  exact TateComparison.HeckeKernel.kernel_injective U (hT.trans (sphericalHeckeFromKernel_kernel U k hk).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HeckeKernel.Construction
