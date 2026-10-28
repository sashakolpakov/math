import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckePushforward
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CosetsKernel
import OAI.RepresentationTheory.Theta.Geometric.Active.Basis

/-! # Retraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Retraction.Local

noncomputable section

/-! Projection onto the active GL3 block is a retraction of the actual
Hecke embedding. The original SL3 inclusion factors through this GL3
algebra with exactly the same kernels. -/

open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Active.Basis.Spherical

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def activeGL3Projection : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SplitGU q s →* RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q where
  toFun g := g.1 v
  map_one' := rfl
  map_mul' _ _ := rfl

theorem activeGL3Projection_integral (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SplitGU q s) (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) :
    activeGL3Projection q v g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q := ((RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.mem_integralSplitGU_iff q g).mp hg).1 v

theorem activeGL3Projection_integral_surjective (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :
    ∃ u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s, activeGL3Projection q v u = g :=
  ⟨CosetsKernel.Local.activeGL3Embedding q v g, (CosetsKernel.Local.activeGL3Embedding_integral_iff q v g).mpr hg,
    CosetsKernel.Local.activeGL3Embedding_self q v g⟩

def activeGL3HeckeRetraction : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) →ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :=
  HeckePushforward.Local.heckePushforward (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (activeGL3Projection q v)
    (activeGL3Projection_integral q v) (activeGL3Projection_integral_surjective q v)

def activeGL3ModuleRetraction : AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) →ₗ[ℚ]
    AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :=
  HeckePushforward.Local.heckeModulePushforward (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (activeGL3Projection q v)
    (activeGL3Projection_integral q v)

theorem activeGL3HeckeRetraction_kernel (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s)) :
    AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) (activeGL3HeckeRetraction q v T) =
      activeGL3ModuleRetraction q v (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) T) :=
  HeckePushforward.Local.heckeOperatorPushforward_kernel _ _ _ _ _ T

theorem activeGL3ModuleRetraction_leftInverse (w : AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    activeGL3ModuleRetraction q v (CosetsKernel.Local.activeGL3ModuleMap q v w) = w := by
  have h : (activeGL3ModuleRetraction q v).comp (CosetsKernel.Local.activeGL3ModuleMap q v) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro c r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    simp [activeGL3ModuleRetraction, CosetsKernel.Local.activeGL3ModuleMap, HeckePushforward.Local.heckeModulePushforward,
      HeckePushforward.Local.heckeCosetPushforward, CosetsKernel.Local.activeGL3CosetMap, activeGL3Projection, CosetsKernel.Local.activeGL3Embedding]
    change Finsupp.single (QuotientGroup.mk ((CosetsKernel.Local.activeGL3Embedding q v g).1 v)) r =
      Finsupp.single (QuotientGroup.mk g) r
    rw [CosetsKernel.Local.activeGL3Embedding_self]
  exact LinearMap.congr_fun h w

theorem activeGL3HeckeRetraction_leftInverse (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)) :
    activeGL3HeckeRetraction q v (CosetsKernel.Local.activeGL3HeckeMap q v T) = T := by
  apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
  rw [activeGL3HeckeRetraction_kernel, CosetsKernel.Local.activeGL3HeckeMap_kernel,
    activeGL3ModuleRetraction_leftInverse]

theorem activeGL3ModuleRetraction_active (w : AbelianScheme.TateComparison.HeckeKernel.CosetModule (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)) :
    CosetsKernel.Local.activeGL3ModuleMap q v (activeGL3ModuleRetraction q v (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeModuleMap q v w)) =
      RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeModuleMap q v w := by
  have h : (CosetsKernel.Local.activeGL3ModuleMap q v).comp
      ((activeGL3ModuleRetraction q v).comp (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeModuleMap q v)) = RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeModuleMap q v := by
    apply Finsupp.lhom_ext
    intro c r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    simp [activeGL3ModuleRetraction, CosetsKernel.Local.activeGL3ModuleMap, HeckePushforward.Local.heckeModulePushforward,
      HeckePushforward.Local.heckeCosetPushforward, CosetsKernel.Local.activeGL3CosetMap, activeGL3Projection, CosetsKernel.Local.activeGL3Embedding,
      RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeModuleMap, RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeCosetMap, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeEmbedding]
    change Finsupp.single
      (QuotientGroup.mk (CosetsKernel.Local.activeGL3Embedding q v ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeEmbedding q v g).1 v))) r =
      Finsupp.single (QuotientGroup.mk (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeEmbedding q v g)) r
    rw [RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeEmbedding_self]
    rfl
  exact LinearMap.congr_fun h w

theorem canonical_activeHeckeMap_kernel (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s)
        (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q v (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v) T) =
      RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeModuleMap q v (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) := by
  have he : RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v T = RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeExtension q v T := by
    calc
      RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v T =
          RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v (RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.activeRestrictionHom q v (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeExtension q v T)) :=
        congrArg (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v) (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeRestriction_extension q v T).symm
      _ = RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeExtension q v T := RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv_restriction q v _
  change AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v T).val = _
  rw [he]
  exact RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.extendActiveOperator_kernel q v T

def sl3ToGL3Hecke : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :=
  (activeGL3HeckeRetraction q v).comp (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q v (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v))

theorem sl3ToGL3Hecke_factorization (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    CosetsKernel.Local.activeGL3HeckeMap q v (sl3ToGL3Hecke q v T) =
      RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q v (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v) T := by
  apply AbelianScheme.TateComparison.HeckeKernel.kernel_injective
  rw [CosetsKernel.Local.activeGL3HeckeMap_kernel]
  change CosetsKernel.Local.activeGL3ModuleMap q v (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)
    (activeGL3HeckeRetraction q v (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q v (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q v) T))) = _
  rw [activeGL3HeckeRetraction_kernel, canonical_activeHeckeMap_kernel,
    activeGL3ModuleRetraction_active]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Retraction.Local
