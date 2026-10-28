import OAI.RepresentationTheory.Theta.Geometric.Active.Cosets

/-! # Cosets Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CosetsKernel.Local

noncomputable section

section

/-! The full active GL3 block and its actual integral cosets inside the
split PEL similitude group. No determinant-unit condition is imposed on
the active block. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def activeGL3Embedding : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q →* RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SplitGU q s where
  toFun g := (fun w => if w = v then g else 1, 1)
  map_one' := by
    apply Prod.ext
    · funext w
      simp
    · rfl
  map_mul' g h := by
    apply Prod.ext
    · funext w
      change (if w = v then g * h else 1) =
        (if w = v then g else 1) * (if w = v then h else 1)
      split_ifs <;> simp
    · simp

theorem activeGL3Embedding_self (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) : (activeGL3Embedding q v g).1 v = g := by
  simp [activeGL3Embedding]

theorem activeGL3Embedding_integral_iff (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    activeGL3Embedding q v g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s ↔ g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q := by
  constructor
  · intro hg
    simpa only [activeGL3Embedding_self] using ((RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.mem_integralSplitGU_iff q _).mp hg).1 v
  · intro hg
    apply (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.mem_integralSplitGU_iff q _).mpr
    refine ⟨?_, (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q).one_mem⟩
    intro w
    change (if w = v then g else 1) ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q
    split_ifs
    · exact hg
    · exact (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q).one_mem

def activeGL3CosetMap : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SplitGU q s ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s :=
  Quotient.map (activeGL3Embedding q v) (by
    intro g h hgh
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv, ← map_mul]
    exact (activeGL3Embedding_integral_iff q v _).mpr (QuotientGroup.leftRel_apply.mp hgh))

theorem activeGL3CosetMap_injective : Function.Injective (activeGL3CosetMap q v) := by
  intro c d
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective d
  intro he
  apply QuotientGroup.eq.mpr
  apply (activeGL3Embedding_integral_iff q v (g⁻¹ * h)).mp
  rw [map_mul, map_inv]
  exact QuotientGroup.eq.mp he

theorem activeGL3CosetMap_smul (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) (c : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :
    activeGL3CosetMap q v (g • c) = activeGL3Embedding q v g • activeGL3CosetMap q v c := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  change QuotientGroup.mk (activeGL3Embedding q v (g * h)) =
    QuotientGroup.mk (activeGL3Embedding q v g * activeGL3Embedding q v h)
  rw [map_mul]

theorem integral_activeGL3_coset_action (k : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s)
    (c : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :
    k.val • activeGL3CosetMap q v c = activeGL3CosetMap q v (k.val.1 v • c) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  apply QuotientGroup.eq.mpr
  apply (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.mem_integralSplitGU_iff q _).mpr
  obtain ⟨hk, hm⟩ := (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.mem_integralSplitGU_iff q k.val).mp k.property
  constructor
  · intro w
    change ((k.val.1 w * (if w = v then g else 1))⁻¹ *
      (if w = v then k.val.1 v * g else 1)) ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q
    by_cases hw : w = v
    · subst w
      simp
    · simpa only [ite_eq_right hw, mul_one] using (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q).inv_mem (hk w)
  · change ((k.val.2 * 1)⁻¹ * 1) ∈ RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q
    simpa only [mul_one] using (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.integralUnits q).inv_mem hm

end

section

/-! Extend actual GL3 spherical kernels into the full PEL algebra.
Integral invariance follows from the literal full-level coset action. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def activeGL3ModuleMap : AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₗ[ℚ] AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) :=
  Finsupp.lmapDomain ℚ ℚ (activeGL3CosetMap q v)

theorem activeGL3ModuleMap_injective : Function.Injective (activeGL3ModuleMap q v) :=
  Finsupp.mapDomain_injective (activeGL3CosetMap_injective q v)

theorem activeGL3ModuleMap_translate (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) (w : AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    activeGL3ModuleMap q v (AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) g w) =
      AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (activeGL3Embedding q v g) (activeGL3ModuleMap q v w) := by
  have h : (activeGL3ModuleMap q v).comp (AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) g) =
      (AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (activeGL3Embedding q v g)).comp (activeGL3ModuleMap q v) := by
    apply Finsupp.lhom_ext
    intro c r
    simp [activeGL3ModuleMap, activeGL3CosetMap_smul]
  exact LinearMap.congr_fun h w

theorem activeGL3ModuleMap_integral_translate (k : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s)
    (w : AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) k.val (activeGL3ModuleMap q v w) =
      activeGL3ModuleMap q v (AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (k.val.1 v) w) := by
  have h : (AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) k.val).comp (activeGL3ModuleMap q v) =
      (activeGL3ModuleMap q v).comp (AbelianScheme.TateComparison.HeckeKernel.translate (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (k.val.1 v)) := by
    apply Finsupp.lhom_ext
    intro c r
    simp [activeGL3ModuleMap, integral_activeGL3_coset_action]
  exact LinearMap.congr_fun h w

theorem activeGL3ModuleMap_identity :
    activeGL3ModuleMap q v (Finsupp.single (QuotientGroup.mk (1 : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q)) 1) =
      Finsupp.single (QuotientGroup.mk (1 : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SplitGU q s)) 1 := by
  change Finsupp.mapDomain (activeGL3CosetMap q v) (Finsupp.single _ _) = _
  rw [Finsupp.mapDomain_single]
  change Finsupp.single (QuotientGroup.mk (activeGL3Embedding q v 1)) 1 = _
  rw [map_one]

def extendGL3Kernel (w : RepresentationTheory.Theta.Geometric.Kernel.Spherical.invariantKernels (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    RepresentationTheory.Theta.Geometric.Kernel.Spherical.invariantKernels (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) :=
  ⟨activeGL3ModuleMap q v w.val, by
    intro k hk
    rw [activeGL3ModuleMap_integral_translate q v ⟨k, hk⟩]
    rw [w.property _ (((RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.mem_integralSplitGU_iff q k).mp hk).1 v)]⟩

def extendGL3Operator (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) :=
  RepresentationTheory.Theta.Geometric.Kernel.Spherical.sphericalOfKernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (extendGL3Kernel q v (RepresentationTheory.Theta.Geometric.Kernel.Spherical.kernelLinearEquiv (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T))

theorem extendGL3Operator_kernel (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (extendGL3Operator q v T) =
      activeGL3ModuleMap q v (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T) :=
  RepresentationTheory.Theta.Geometric.Kernel.Spherical.kernel_sphericalOfKernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) _

theorem extendGL3Operator_transport (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q))
    (w : AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    (extendGL3Operator q v T).val (activeGL3ModuleMap q v w) =
      activeGL3ModuleMap q v (T.val w) := by
  have hs (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
      (extendGL3Operator q v T).val
        (activeGL3ModuleMap q v (Finsupp.single (QuotientGroup.mk g) 1)) =
        activeGL3ModuleMap q v (T.val (Finsupp.single (QuotientGroup.mk g) 1)) := by
    change (extendGL3Operator q v T).val
      (Finsupp.mapDomain (activeGL3CosetMap q v) (Finsupp.single _ _)) = _
    rw [Finsupp.mapDomain_single]
    change (extendGL3Operator q v T).val
      (Finsupp.single (QuotientGroup.mk (activeGL3Embedding q v g)) 1) = _
    rw [AbelianScheme.TateComparison.HeckeKernel.hecke_single, extendGL3Operator_kernel, ← activeGL3ModuleMap_translate, ← AbelianScheme.TateComparison.HeckeKernel.hecke_single]
  have he : (extendGL3Operator q v T).val.comp (activeGL3ModuleMap q v) =
      (activeGL3ModuleMap q v).comp T.val := by
    apply Finsupp.lhom_ext
    intro c r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    change (extendGL3Operator q v T).val
      (activeGL3ModuleMap q v (Finsupp.single (QuotientGroup.mk g) r)) =
      activeGL3ModuleMap q v (T.val (Finsupp.single (QuotientGroup.mk g) r))
    rw [← Finsupp.smul_single_one (QuotientGroup.mk g) r]
    simp only [map_smul, hs]
  exact LinearMap.congr_fun he w

end

/-! The full active GL3 spherical algebra embeds in the actual full PEL
Hecke algebra. Multiplication is proved on the original kernel action. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def activeGL3HeckeMap : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) →ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) where
  toFun := extendGL3Operator q v
  map_zero' := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [extendGL3Operator_kernel]
    exact map_zero (activeGL3ModuleMap q v)
  map_one' := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [extendGL3Operator_kernel]
    exact activeGL3ModuleMap_identity q v
  map_add' T U := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [extendGL3Operator_kernel]
    change activeGL3ModuleMap q v (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T + AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) U) =
      AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (extendGL3Operator q v T) +
        AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (extendGL3Operator q v U)
    rw [map_add, extendGL3Operator_kernel, extendGL3Operator_kernel]
  map_mul' T U := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [extendGL3Operator_kernel]
    change activeGL3ModuleMap q v (T.val (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) U)) =
      (extendGL3Operator q v T).val (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (extendGL3Operator q v U))
    rw [extendGL3Operator_kernel, extendGL3Operator_transport]
  commutes' r := by
    apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
    rw [extendGL3Operator_kernel]
    change activeGL3ModuleMap q v (r • Finsupp.single (QuotientGroup.mk (1 : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q)) 1) =
      r • Finsupp.single (QuotientGroup.mk (1 : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SplitGU q s)) 1
    rw [map_smul, activeGL3ModuleMap_identity]

theorem activeGL3HeckeMap_kernel (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (activeGL3HeckeMap q v T) =
      activeGL3ModuleMap q v (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T) := extendGL3Operator_kernel q v T

theorem activeGL3HeckeMap_injective : Function.Injective (activeGL3HeckeMap q v) := by
  intro T U h
  apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)
  apply activeGL3ModuleMap_injective q v
  simpa only [activeGL3HeckeMap_kernel] using congrArg (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s)) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CosetsKernel.Local
