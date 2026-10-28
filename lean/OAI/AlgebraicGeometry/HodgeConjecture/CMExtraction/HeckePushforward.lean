import OAI.RepresentationTheory.Theta.Geometric.Kernel

/-! # Hecke Pushforward -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckePushforward.Local

noncomputable section

/-! Push actual spherical operators along a group homomorphism mapping
the integral subgroup onto the target integral subgroup. The map sums
coefficients on coset fibres and intertwines the original operators. -/

open scoped Classical

variable {G H : Type*} [Group G] [Group H] (U : Subgroup G) (V : Subgroup H)
  (f : G →* H) (hf : ∀ u ∈ U, f u ∈ V)

def heckeCosetPushforward : G ⧸ U → H ⧸ V :=
  Quotient.map f (by
    intro g h hgh
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact hf _ (QuotientGroup.leftRel_apply.mp hgh))

theorem heckeCosetPushforward_smul (g : G) (c : G ⧸ U) :
    heckeCosetPushforward U V f hf (g • c) =
      f g • heckeCosetPushforward U V f hf c := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  change QuotientGroup.mk (f (g * h)) = QuotientGroup.mk (f g * f h)
  rw [map_mul]

def heckeModulePushforward : AbelianScheme.TateComparison.HeckeKernel.CosetModule U →ₗ[ℚ] AbelianScheme.TateComparison.HeckeKernel.CosetModule V :=
  Finsupp.lmapDomain ℚ ℚ (heckeCosetPushforward U V f hf)

theorem heckeModulePushforward_translate (g : G) (w : AbelianScheme.TateComparison.HeckeKernel.CosetModule U) :
    heckeModulePushforward U V f hf (AbelianScheme.TateComparison.HeckeKernel.translate U g w) =
      AbelianScheme.TateComparison.HeckeKernel.translate V (f g) (heckeModulePushforward U V f hf w) := by
  have h : (heckeModulePushforward U V f hf).comp (AbelianScheme.TateComparison.HeckeKernel.translate U g) =
      (AbelianScheme.TateComparison.HeckeKernel.translate V (f g)).comp (heckeModulePushforward U V f hf) := by
    apply Finsupp.lhom_ext
    intro c r
    simp [heckeModulePushforward, heckeCosetPushforward_smul]
  exact LinearMap.congr_fun h w

theorem heckeModulePushforward_identity :
    heckeModulePushforward U V f hf (Finsupp.single (QuotientGroup.mk (1 : G)) 1) =
      Finsupp.single (QuotientGroup.mk (1 : H)) 1 := by
  change Finsupp.mapDomain _ (Finsupp.single _ _) = _
  rw [Finsupp.mapDomain_single]
  change Finsupp.single (QuotientGroup.mk (f 1)) 1 = _
  rw [map_one]

variable (hs : ∀ v ∈ V, ∃ u ∈ U, f u = v)

def heckeKernelPushforward (w : RepresentationTheory.Theta.Geometric.Kernel.Spherical.invariantKernels U) : RepresentationTheory.Theta.Geometric.Kernel.Spherical.invariantKernels V :=
  ⟨heckeModulePushforward U V f hf w.val, by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hs v hv
    rw [← heckeModulePushforward_translate, w.property u hu]⟩

def heckeOperatorPushforward (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra U) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra V :=
  RepresentationTheory.Theta.Geometric.Kernel.Spherical.sphericalOfKernel V (heckeKernelPushforward U V f hf hs (RepresentationTheory.Theta.Geometric.Kernel.Spherical.kernelLinearEquiv U T))

theorem heckeOperatorPushforward_kernel (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra U) :
    AbelianScheme.TateComparison.HeckeKernel.kernel V (heckeOperatorPushforward U V f hf hs T) =
      heckeModulePushforward U V f hf (AbelianScheme.TateComparison.HeckeKernel.kernel U T) := RepresentationTheory.Theta.Geometric.Kernel.Spherical.kernel_sphericalOfKernel V _

theorem heckeOperatorPushforward_transport (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra U) (w : AbelianScheme.TateComparison.HeckeKernel.CosetModule U) :
    (heckeOperatorPushforward U V f hf hs T).val (heckeModulePushforward U V f hf w) =
      heckeModulePushforward U V f hf (T.val w) := by
  have hd (g : G) :
      (heckeOperatorPushforward U V f hf hs T).val
          (heckeModulePushforward U V f hf (Finsupp.single (QuotientGroup.mk g) 1)) =
        heckeModulePushforward U V f hf (T.val (Finsupp.single (QuotientGroup.mk g) 1)) := by
    change (heckeOperatorPushforward U V f hf hs T).val
      (Finsupp.mapDomain _ (Finsupp.single _ _)) = _
    rw [Finsupp.mapDomain_single]
    change (heckeOperatorPushforward U V f hf hs T).val
      (Finsupp.single (QuotientGroup.mk (f g)) 1) = _
    rw [AbelianScheme.TateComparison.HeckeKernel.hecke_single, heckeOperatorPushforward_kernel,
      ← heckeModulePushforward_translate, ← AbelianScheme.TateComparison.HeckeKernel.hecke_single]
  have h : (heckeOperatorPushforward U V f hf hs T).val.comp
      (heckeModulePushforward U V f hf) = (heckeModulePushforward U V f hf).comp T.val := by
    apply Finsupp.lhom_ext
    intro c r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    change (heckeOperatorPushforward U V f hf hs T).val
      (heckeModulePushforward U V f hf (Finsupp.single (QuotientGroup.mk g) r)) =
      heckeModulePushforward U V f hf (T.val (Finsupp.single (QuotientGroup.mk g) r))
    rw [← Finsupp.smul_single_one (QuotientGroup.mk g) r]
    simp only [map_smul, hd]
  exact LinearMap.congr_fun h w

def heckePushforward : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra U →ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra V where
  toFun := heckeOperatorPushforward U V f hf hs
  map_zero' := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [heckeOperatorPushforward_kernel]
    exact map_zero (heckeModulePushforward U V f hf)
  map_one' := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [heckeOperatorPushforward_kernel]
    exact heckeModulePushforward_identity U V f hf
  map_add' T S := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [heckeOperatorPushforward_kernel]
    change heckeModulePushforward U V f hf (AbelianScheme.TateComparison.HeckeKernel.kernel U T + AbelianScheme.TateComparison.HeckeKernel.kernel U S) =
      AbelianScheme.TateComparison.HeckeKernel.kernel V (heckeOperatorPushforward U V f hf hs T) +
        AbelianScheme.TateComparison.HeckeKernel.kernel V (heckeOperatorPushforward U V f hf hs S)
    rw [map_add, heckeOperatorPushforward_kernel, heckeOperatorPushforward_kernel]
  map_mul' T S := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [heckeOperatorPushforward_kernel]
    change heckeModulePushforward U V f hf (T.val (AbelianScheme.TateComparison.HeckeKernel.kernel U S)) =
      (heckeOperatorPushforward U V f hf hs T).val
        (AbelianScheme.TateComparison.HeckeKernel.kernel V (heckeOperatorPushforward U V f hf hs S))
    rw [heckeOperatorPushforward_kernel, heckeOperatorPushforward_transport]
  commutes' r := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [heckeOperatorPushforward_kernel]
    change heckeModulePushforward U V f hf
      (r • Finsupp.single (QuotientGroup.mk (1 : G)) 1) =
        r • Finsupp.single (QuotientGroup.mk (1 : H)) 1
    rw [map_smul, heckeModulePushforward_identity]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckePushforward.Local
