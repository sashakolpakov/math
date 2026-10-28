import OAI.RepresentationTheory.Theta.Geometric.Active.Cosets
import OAI.RepresentationTheory.Theta.Geometric.KernelCoefficients

/-! # Integral Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntegralKernel.Spherical

noncomputable section

/-! Full integral invariance of a kernel extended from the SL3 active
block. The proof uses the actual GL3/SL3 double-coset comparison from ElementaryDivisors. -/

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

theorem activeOrbit_smul_iff (k : SphericalGU.Spherical.SplitGU q s) (hk : k ∈ SphericalGU.Spherical.integralSplitGU q s)
    (c : SphericalGU.Spherical.SplitGU q s ⧸ SphericalGU.Spherical.integralSplitGU q s) :
    k • c ∈ SphericalGU.Spherical.activeOrbit q v ↔ c ∈ SphericalGU.Spherical.activeOrbit q v := by
  have hkH : k ∈ SphericalGU.Spherical.activeSector q v :=
    (show SphericalGU.Spherical.integralSplitGU q s ≤ SphericalGU.Spherical.activeSector q v from le_sup_left) hk
  constructor
  · rintro ⟨g, hg, hgc⟩
    refine ⟨k⁻¹ * g, (SphericalGU.Spherical.activeSector q v).mul_mem ((SphericalGU.Spherical.activeSector q v).inv_mem hkH) hg, ?_⟩
    change k⁻¹ • QuotientGroup.mk g = c
    rw [hgc, inv_smul_smul]
  · rintro ⟨g, hg, hgc⟩
    refine ⟨k * g, (SphericalGU.Spherical.activeSector q v).mul_mem hkH hg, ?_⟩
    change k • QuotientGroup.mk g = k • c
    rw [hgc]

theorem activeModuleMap_apply (w : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q))
    (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) : Active.Cosets.Spherical.activeModuleMap q v w (Active.Cosets.Spherical.activeCosetMap q v c) = w c :=
  Finsupp.mapDomain_apply_of_injective (Active.Cosets.Spherical.activeCosetMap_injective q v) w c

theorem activeModuleMap_zero_outside (w : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q))
    (c : SphericalGU.Spherical.SplitGU q s ⧸ SphericalGU.Spherical.integralSplitGU q s) (hc : c ∉ SphericalGU.Spherical.activeOrbit q v) :
    Active.Cosets.Spherical.activeModuleMap q v w c = 0 := by
  have hw : Active.Cosets.Spherical.activeModuleMap q v w ∈ SphericalGU.Spherical.activeCosetModule q v := by
    rw [← Active.Cosets.Spherical.activeModuleEquiv_coe]
    exact (Active.Cosets.Spherical.activeModuleEquiv q v w).property
  exact (Finsupp.mem_supported' ℚ _).mp hw c hc

theorem active_integral_orbit_doubleCoset (k : SphericalGU.Spherical.integralSplitGU q s) (g h : SphericalGU.Spherical.SL3 q)
    (he : Active.Cosets.Spherical.activeCosetMap q v (QuotientGroup.mk h) =
      k.val • Active.Cosets.Spherical.activeCosetMap q v (QuotientGroup.mk g)) :
    DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q) g h := by
  have hfull := KernelCoefficients.Spherical.doubleCoset_of_coset_smul (SphericalGU.Spherical.integralSplitGU q s)
    (SphericalGU.Spherical.activeEmbedding q v g) (SphericalGU.Spherical.activeEmbedding q v h) k.val k.property he
  obtain ⟨a, b, hab⟩ := hfull
  apply (DoubleCosets.Spherical.special_doubleCoset_iff q g h).mp
  refine ⟨⟨a.val.1 v, ((Active.Cosets.Spherical.mem_integralSplitGU_iff q a.val).mp a.property).1 v⟩,
    ⟨b.val.1 v, ((Active.Cosets.Spherical.mem_integralSplitGU_iff q b.val).mp b.property).1 v⟩, ?_⟩
  have hmatrix := congrArg (fun z : SphericalGU.Spherical.SplitGU q s => z.1 v) hab
  change (SphericalGU.Spherical.activeEmbedding q v h).1 v = a.val.1 v * (SphericalGU.Spherical.activeEmbedding q v g).1 v * b.val.1 v at hmatrix
  simpa only [Active.Cosets.Spherical.activeEmbedding_self] using hmatrix

theorem activeModuleMap_integral_invariant (w : Kernel.Spherical.invariantKernels (SphericalGU.Spherical.integralSL3 q))
    (k : SphericalGU.Spherical.SplitGU q s) (hk : k ∈ SphericalGU.Spherical.integralSplitGU q s) :
    AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSplitGU q s) k (Active.Cosets.Spherical.activeModuleMap q v w.val) = Active.Cosets.Spherical.activeModuleMap q v w.val := by
  ext c
  rw [KernelCoefficients.Spherical.translate_apply]
  by_cases hc : c ∈ SphericalGU.Spherical.activeOrbit q v
  · have hd : k⁻¹ • c ∈ SphericalGU.Spherical.activeOrbit q v :=
      (activeOrbit_smul_iff q v k⁻¹ ((SphericalGU.Spherical.integralSplitGU q s).inv_mem hk) c).mpr hc
    let c0 := (Active.Cosets.Spherical.activeCosetEquiv q v).symm ⟨c, hc⟩
    let d0 := (Active.Cosets.Spherical.activeCosetEquiv q v).symm ⟨k⁻¹ • c, hd⟩
    have hc0 := congrArg Subtype.val ((Active.Cosets.Spherical.activeCosetEquiv q v).apply_symm_apply ⟨c, hc⟩)
    have hd0 := congrArg Subtype.val ((Active.Cosets.Spherical.activeCosetEquiv q v).apply_symm_apply ⟨k⁻¹ • c, hd⟩)
    change Active.Cosets.Spherical.activeCosetMap q v c0 = c at hc0
    change Active.Cosets.Spherical.activeCosetMap q v d0 = k⁻¹ • c at hd0
    rw [← hd0, ← hc0, activeModuleMap_apply, activeModuleMap_apply]
    have hdouble := active_integral_orbit_doubleCoset q v
      ⟨k⁻¹, (SphericalGU.Spherical.integralSplitGU q s).inv_mem hk⟩ c0.out d0.out (by
        simp only [QuotientGroup.out_eq']
        rw [hd0, hc0])
    simpa only [QuotientGroup.out_eq'] using
      KernelCoefficients.Spherical.invariantKernel_doubleCoset (SphericalGU.Spherical.integralSL3 q) w c0.out d0.out hdouble
  · have hd : k⁻¹ • c ∉ SphericalGU.Spherical.activeOrbit q v :=
      fun h => hc ((activeOrbit_smul_iff q v k⁻¹ ((SphericalGU.Spherical.integralSplitGU q s).inv_mem hk) c).mp h)
    rw [activeModuleMap_zero_outside q v w.val _ hd, activeModuleMap_zero_outside q v w.val c hc]

def extendActiveKernel (w : Kernel.Spherical.invariantKernels (SphericalGU.Spherical.integralSL3 q)) :
    Kernel.Spherical.invariantKernels (SphericalGU.Spherical.integralSplitGU q s) :=
  ⟨Active.Cosets.Spherical.activeModuleMap q v w.val, activeModuleMap_integral_invariant q v w⟩

end

end OAI.RepresentationTheory.Theta.Geometric.IntegralKernel.Spherical
