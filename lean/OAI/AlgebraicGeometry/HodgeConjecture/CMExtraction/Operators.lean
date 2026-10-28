import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CosetsKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Operators.Local

noncomputable section

/-! The active GL3 embedding preserves the original unnormalized double
coset operators, including their characteristic-function coefficients. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

theorem activeGL3_doubleCosetOrbit (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    AbelianScheme.TateComparison.HeckeKernel.doubleCosetOrbit (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (CosetsKernel.Local.activeGL3Embedding q v g) =
      CosetsKernel.Local.activeGL3CosetMap q v '' AbelianScheme.TateComparison.HeckeKernel.doubleCosetOrbit (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) g := by
  ext c
  constructor
  · rintro ⟨k, rfl⟩
    let l : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q :=
      ⟨k.val.1 v, ((RepresentationTheory.Theta.Geometric.Active.Cosets.Spherical.mem_integralSplitGU_iff q k.val).mp k.property).1 v⟩
    refine ⟨l.val • QuotientGroup.mk g⁻¹, ⟨l, rfl⟩, ?_⟩
    rw [← map_inv]
    exact (CosetsKernel.Local.integral_activeGL3_coset_action q v k (QuotientGroup.mk g⁻¹)).symm
  · rintro ⟨c, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨CosetsKernel.Local.activeGL3Embedding q v k.val,
      (CosetsKernel.Local.activeGL3Embedding_integral_iff q v k.val).mpr k.property⟩, ?_⟩
    rw [CosetsKernel.Local.activeGL3CosetMap_smul]
    change CosetsKernel.Local.activeGL3Embedding q v k.val • QuotientGroup.mk (CosetsKernel.Local.activeGL3Embedding q v g)⁻¹ =
      CosetsKernel.Local.activeGL3Embedding q v k.val • QuotientGroup.mk (CosetsKernel.Local.activeGL3Embedding q v g⁻¹)
    rw [map_inv]

theorem gl3_doubleCosetOrbit_finite (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    (AbelianScheme.TateComparison.HeckeKernel.doubleCosetOrbit (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) g).Finite := by
  have hf := AbelianScheme.TateComparison.CentralConvolution.doubleCosetOrbit_finite (AbelianScheme.TateComparison.HeckeKernel.integralLevel 1 q)
    (AbelianScheme.TateComparison.CentralConvolution.integralLevel_compact 1 q) (AbelianScheme.TateComparison.CentralConvolution.integralLevel_open 1 q)
    (CosetsKernel.Local.activeGL3Embedding q (0 : Fin 1) g)
  rw [activeGL3_doubleCosetOrbit] at hf
  exact hf.of_finite_image (CosetsKernel.Local.activeGL3CosetMap_injective q (0 : Fin 1)).injOn

def rawGL3Hecke (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) :=
  AbelianScheme.TateComparison.HeckeKernel.rawHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) g (gl3_doubleCosetOrbit_finite q g)

theorem rawGL3Hecke_isRaw (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) g (rawGL3Hecke q g) := AbelianScheme.TateComparison.HeckeKernel.rawHecke_isRaw _ _ _

theorem activeGL3HeckeMap_isRaw {g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q} {T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.algebra (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q)}
    (hT : AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) g T) :
    AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (CosetsKernel.Local.activeGL3Embedding q v g)
      (CosetsKernel.Local.activeGL3HeckeMap q v T) := by
  intro x
  rw [← AbelianScheme.TateComparison.HeckeKernel.mem_doubleCosetOrbit, activeGL3_doubleCosetOrbit]
  rw [CosetsKernel.Local.activeGL3HeckeMap_kernel]
  change Finsupp.mapDomain (CosetsKernel.Local.activeGL3CosetMap q v)
    (AbelianScheme.TateComparison.HeckeKernel.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) T) (QuotientGroup.mk x) = _
  by_cases hx : (QuotientGroup.mk x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SplitGU q s ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) ∈
      Set.range (CosetsKernel.Local.activeGL3CosetMap q v)
  · obtain ⟨c, hc⟩ := hx
    rw [← hc, Finsupp.mapDomain_apply_of_injective (CosetsKernel.Local.activeGL3CosetMap_injective q v), AbelianScheme.TateComparison.HeckeKernel.raw_kernel_at _ hT]
    simp only [Set.mem_image, (CosetsKernel.Local.activeGL3CosetMap_injective q v).eq_iff, exists_eq_right]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hx, ite_eq_right]
    exact fun h => hx (Set.mem_range.mpr ⟨_, h.choose_spec.2⟩)

theorem activeGL3HeckeMap_raw (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) :
    CosetsKernel.Local.activeGL3HeckeMap q v (rawGL3Hecke q g) =
      AbelianScheme.TateComparison.HeckeKernel.rawHecke (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSplitGU q s) (CosetsKernel.Local.activeGL3Embedding q v g)
        (AbelianScheme.TateComparison.CentralConvolution.doubleCosetOrbit_finite (AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AbelianScheme.TateComparison.CentralConvolution.integralLevel_compact s q)
          (AbelianScheme.TateComparison.CentralConvolution.integralLevel_open s q) _) :=
  AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique _ (activeGL3HeckeMap_isRaw q v (rawGL3Hecke_isRaw q g))
    (AbelianScheme.TateComparison.HeckeKernel.rawHecke_isRaw _ _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Operators.Local
