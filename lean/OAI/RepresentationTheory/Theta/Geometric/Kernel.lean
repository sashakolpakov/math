import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.Kernel.Spherical

noncomputable section

/-! Construct a spherical operator from its finite, integral-invariant
identity column. This supplies the inverse to TateComparison's injective kernel map. -/

variable {G : Type*} [Group G] (K : Subgroup G)

def invariantKernels : Submodule ℚ (SphericalGU.Spherical.CosetModule K) where
  carrier := {v | ∀ k ∈ K, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K k v = v}
  zero_mem' := by intro k hk; exact map_zero _
  add_mem' := by intro v w hv hw k hk; simp [hv k hk, hw k hk]
  smul_mem' := by intro r v hv k hk; simp [hv k hk]

def translatedKernel (v : invariantKernels K) : G ⧸ K → SphericalGU.Spherical.CosetModule K :=
  Quotient.lift (fun g => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g v.val) (by
    intro g h hgh
    have hk := QuotientGroup.leftRel_apply.mp hgh
    have hv := v.property (g⁻¹ * h) hk
    calc
      AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g v.val = AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K (g⁻¹ * h) v.val) := by rw [hv]
      _ = AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K h v.val := by
        rw [← Module.End.mul_apply, ← AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate_mul, mul_inv_cancel_left])

@[simp] theorem translatedKernel_mk (v : invariantKernels K) (g : G) :
    translatedKernel K v (QuotientGroup.mk g) = AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g v.val := rfl

theorem translatedKernel_smul (v : invariantKernels K) (g : G) (c : G ⧸ K) :
    translatedKernel K v (g • c) = AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g (translatedKernel K v c) := by
  induction c using Quotient.inductionOn with
  | h h =>
    change AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K (g * h) v.val = AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K h v.val)
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate_mul]
    rfl

def kernelOperator (v : invariantKernels K) : Module.End ℚ (SphericalGU.Spherical.CosetModule K) :=
  Finsupp.linearCombination ℚ (translatedKernel K v)

@[simp] theorem kernelOperator_single (v : invariantKernels K) (c : G ⧸ K) (r : ℚ) :
    kernelOperator K v (Finsupp.single c r) = r • translatedKernel K v c := by
  simp [kernelOperator]

def sphericalOfKernel (v : invariantKernels K) : SphericalGU.Spherical.algebra K :=
  ⟨kernelOperator K v, by
    rintro _ ⟨g, rfl⟩
    apply Finsupp.lhom_ext
    intro c r
    change AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g (kernelOperator K v (Finsupp.single c r)) =
      kernelOperator K v (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate K g (Finsupp.single c r))
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate_single, kernelOperator_single, kernelOperator_single,
      translatedKernel_smul, map_smul]⟩

@[simp] theorem kernel_sphericalOfKernel (v : invariantKernels K) :
    SphericalGU.Spherical.kernel K (sphericalOfKernel K v) = v.val := by
  change kernelOperator K v (Finsupp.single (QuotientGroup.mk (1 : G)) 1) = v.val
  rw [kernelOperator_single, one_smul, translatedKernel_mk, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate_one]
  rfl

def kernelLinearEquiv : SphericalGU.Spherical.algebra K ≃ₗ[ℚ] invariantKernels K where
  toFun T := ⟨SphericalGU.Spherical.kernel K T, SphericalGU.Spherical.kernel_fixed K T⟩
  invFun := sphericalOfKernel K
  left_inv T := by
    apply AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel_injective K
    exact kernel_sphericalOfKernel K _
  right_inv v := by apply Subtype.ext; exact kernel_sphericalOfKernel K v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Kernel.Spherical
