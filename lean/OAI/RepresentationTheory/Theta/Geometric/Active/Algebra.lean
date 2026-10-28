import OAI.RepresentationTheory.Theta.Geometric.Active.Cosets
import OAI.RepresentationTheory.Theta.Geometric.IntegralKernel

/-! # Algebra -/

namespace OAI.RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical

noncomputable section

section

/-! The active convolution-algebra equivalence. The inverse extends the
finite identity column by zero, uses the proved full integral invariance,
and reconstructs the full spherical operator. Multiplication is preserved
by the already constructed restriction algebra homomorphism. -/

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def extendActiveOperator (T : SphericalGU.Spherical.SL3Hecke q) : SphericalGU.Spherical.FullHecke q s :=
  Kernel.Spherical.sphericalOfKernel (SphericalGU.Spherical.integralSplitGU q s)
    (IntegralKernel.Spherical.extendActiveKernel q v (Kernel.Spherical.kernelLinearEquiv (SphericalGU.Spherical.integralSL3 q) T))

theorem extendActiveOperator_kernel (T : SphericalGU.Spherical.SL3Hecke q) :
    SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) (extendActiveOperator q v T) =
      Cosets.Spherical.activeModuleMap q v (SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSL3 q) T) :=
  Kernel.Spherical.kernel_sphericalOfKernel (SphericalGU.Spherical.integralSplitGU q s) _

theorem extendActiveOperator_transport (T : SphericalGU.Spherical.SL3Hecke q) (w : SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q)) :
    (extendActiveOperator q v T).val (Cosets.Spherical.activeModuleMap q v w) = Cosets.Spherical.activeModuleMap q v (T.val w) := by
  have hsingle (g : SphericalGU.Spherical.SL3 q) :
      (extendActiveOperator q v T).val
        (Cosets.Spherical.activeModuleMap q v (Finsupp.single (QuotientGroup.mk g) 1)) =
      Cosets.Spherical.activeModuleMap q v (T.val (Finsupp.single (QuotientGroup.mk g) 1)) := by
    change (extendActiveOperator q v T).val
      (Finsupp.mapDomain (Cosets.Spherical.activeCosetMap q v) (Finsupp.single (QuotientGroup.mk g) 1)) = _
    rw [Finsupp.mapDomain_single]
    change (extendActiveOperator q v T).val
      (Finsupp.single (QuotientGroup.mk (SphericalGU.Spherical.activeEmbedding q v g)) 1) = _
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.hecke_single]
    exact (congrArg (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.translate (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g))
      (extendActiveOperator_kernel q v T)).trans
        ((Cosets.Spherical.activeModuleMap_translate q v g (SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSL3 q) T)).symm.trans
          (congrArg (Cosets.Spherical.activeModuleMap q v) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.hecke_single (SphericalGU.Spherical.integralSL3 q) T g).symm))
  have he : (extendActiveOperator q v T).val.comp (Cosets.Spherical.activeModuleMap q v) =
      (Cosets.Spherical.activeModuleMap q v).comp T.val := by
    apply Finsupp.lhom_ext
    intro c r
    induction c using Quotient.inductionOn with
    | h g =>
      change (extendActiveOperator q v T).val
        (Cosets.Spherical.activeModuleMap q v (Finsupp.single (QuotientGroup.mk g) r)) =
        Cosets.Spherical.activeModuleMap q v (T.val (Finsupp.single (QuotientGroup.mk g) r))
      rw [← Finsupp.smul_single_one (QuotientGroup.mk g) r]
      simp only [map_smul, hsingle]
  exact LinearMap.congr_fun he w

def activeExtension (T : SphericalGU.Spherical.SL3Hecke q) : SphericalGU.Spherical.activeAlgebra q v :=
  ⟨extendActiveOperator q v T, by
    intro w hw
    let u := (Cosets.Spherical.activeModuleEquiv q v).symm ⟨w, hw⟩
    have hu : Cosets.Spherical.activeModuleMap q v u = w := by
      rw [← Cosets.Spherical.activeModuleEquiv_coe]
      exact congrArg Subtype.val ((Cosets.Spherical.activeModuleEquiv q v).apply_symm_apply ⟨w, hw⟩)
    rw [← hu, extendActiveOperator_transport, ← Cosets.Spherical.activeModuleEquiv_coe]
    exact (Cosets.Spherical.activeModuleEquiv q v (T.val u)).property⟩

theorem activeRestriction_extension (T : SphericalGU.Spherical.SL3Hecke q) :
    Cosets.Spherical.activeRestrictionHom q v (activeExtension q v T) = T := by
  apply AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel_injective (SphericalGU.Spherical.integralSL3 q)
  apply Cosets.Spherical.activeModuleMap_injective q v
  rw [Cosets.Spherical.activeRestriction_kernel]
  exact extendActiveOperator_kernel q v T

theorem activeRestriction_surjective : Function.Surjective (Cosets.Spherical.activeRestrictionHom q v) :=
  fun T => ⟨activeExtension q v T, activeRestriction_extension q v T⟩

/-- Full integral invariance and convolution multiplication are proved;
the equivalence is not a candidate field or an additional hypothesis. -/
def activeHeckeEquiv : SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] SphericalGU.Spherical.activeAlgebra q v :=
  (AlgEquiv.ofBijective (Cosets.Spherical.activeRestrictionHom q v)
    ⟨Cosets.Spherical.activeRestriction_injective q v, activeRestriction_surjective q v⟩).symm

end

/-! Support of a full spherical identity column in the active orbit is
equivalent to preservation of the active coset module. -/

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

def supportedKernelPreimage (T : SphericalGU.Spherical.FullHecke q s)
    (hT : SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T ∈ SphericalGU.Spherical.activeCosetModule q v) :
    SphericalGU.Spherical.CosetModule (SphericalGU.Spherical.integralSL3 q) :=
  (Cosets.Spherical.activeModuleEquiv q v).symm ⟨SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T, hT⟩

theorem supportedKernelPreimage_map (T : SphericalGU.Spherical.FullHecke q s)
    (hT : SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T ∈ SphericalGU.Spherical.activeCosetModule q v) :
    Cosets.Spherical.activeModuleMap q v (supportedKernelPreimage q v T hT) = SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T := by
  rw [← Cosets.Spherical.activeModuleEquiv_coe]
  exact congrArg Subtype.val ((Cosets.Spherical.activeModuleEquiv q v).apply_symm_apply _)

def supportedInvariantKernel (T : SphericalGU.Spherical.FullHecke q s)
    (hT : SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T ∈ SphericalGU.Spherical.activeCosetModule q v) :
    Kernel.Spherical.invariantKernels (SphericalGU.Spherical.integralSL3 q) :=
  ⟨supportedKernelPreimage q v T hT, by
    intro k hk
    apply Cosets.Spherical.activeModuleMap_injective q v
    rw [Cosets.Spherical.activeModuleMap_translate, supportedKernelPreimage_map]
    exact SphericalGU.Spherical.kernel_fixed (SphericalGU.Spherical.integralSplitGU q s) T (SphericalGU.Spherical.activeEmbedding q v k)
      ((Cosets.Spherical.activeEmbedding_integral_iff q v k).mpr hk)⟩

theorem supported_kernel_mem_active (T : SphericalGU.Spherical.FullHecke q s)
    (hT : SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSplitGU q s) T ∈ SphericalGU.Spherical.activeCosetModule q v) :
    T ∈ SphericalGU.Spherical.activeAlgebra q v := by
  let S := Kernel.Spherical.sphericalOfKernel (SphericalGU.Spherical.integralSL3 q) (supportedInvariantKernel q v T hT)
  have he : (activeExtension q v S).val = T := by
    apply AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel_injective (SphericalGU.Spherical.integralSplitGU q s)
    have h := extendActiveOperator_kernel q v S
    have hsmall : SphericalGU.Spherical.kernel (SphericalGU.Spherical.integralSL3 q) S = supportedKernelPreimage q v T hT :=
      Kernel.Spherical.kernel_sphericalOfKernel (SphericalGU.Spherical.integralSL3 q) _
    exact h.trans ((congrArg (Cosets.Spherical.activeModuleMap q v) hsmall).trans (supportedKernelPreimage_map q v T hT))
  rw [← he]
  exact (activeExtension q v S).property

theorem raw_active_mem_active (g : SphericalGU.Spherical.SplitGU q s) (hg : g ∈ SphericalGU.Spherical.activeSector q v)
    (T : SphericalGU.Spherical.FullHecke q s) (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset (SphericalGU.Spherical.integralSplitGU q s) g T) :
    T ∈ SphericalGU.Spherical.activeAlgebra q v := by
  apply supported_kernel_mem_active q v T
  apply (Finsupp.mem_supported' ℚ _).mpr
  intro c hc
  have hnot : ¬ ∃ k l : SphericalGU.Spherical.integralSplitGU q s, c.out = k.val * g⁻¹ * l.val := by
    rintro ⟨k, l, he⟩
    apply hc
    refine ⟨c.out, ?_, QuotientGroup.out_eq' c⟩
    rw [he]
    apply (SphericalGU.Spherical.activeSector q v).mul_mem
    · apply (SphericalGU.Spherical.activeSector q v).mul_mem
      · exact (show SphericalGU.Spherical.integralSplitGU q s ≤ SphericalGU.Spherical.activeSector q v from le_sup_left) k.property
      · exact (SphericalGU.Spherical.activeSector q v).inv_mem hg
    · exact (show SphericalGU.Spherical.integralSplitGU q s ≤ SphericalGU.Spherical.activeSector q v from le_sup_left) l.property
  have h := hT c.out
  simpa only [QuotientGroup.out_eq', ite_eq_right hnot] using h

@[simp] theorem activeHeckeEquiv_restriction (T : SphericalGU.Spherical.activeAlgebra q v) :
    activeHeckeEquiv q v (Cosets.Spherical.activeRestrictionHom q v T) = T :=
  (AlgEquiv.ofBijective (Cosets.Spherical.activeRestrictionHom q v)
    ⟨Cosets.Spherical.activeRestriction_injective q v, activeRestriction_surjective q v⟩).symm_apply_apply T

end

end OAI.RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical
