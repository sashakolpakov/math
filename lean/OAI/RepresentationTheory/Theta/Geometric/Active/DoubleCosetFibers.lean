import OAI.RepresentationTheory.Theta.Geometric.Active.Basis
import OAI.RepresentationTheory.Theta.Geometric.CosetShift

/-! # Double Coset Fibers -/

namespace OAI.RepresentationTheory.Theta.Geometric.Active.DoubleCosetFibers.Spherical

noncomputable section

/-! The active embedding identifies each individual raw SL3 coset support
with the corresponding full split support. Central clearing retains this bijection. -/

def rawSupportDoubleCosetEquiv {G : Type*} [Group G] (U : Subgroup G) (g : G) :
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U g ≃ DoubleCosets.Spherical.DoubleCosetFiber U g⁻¹ :=
  (Equiv.refl (G ⧸ U)).subtypeEquiv (by
    intro c
    constructor
    · intro hc
      induction c using Quotient.inductionOn with
      | h h => exact ⟨h, rfl, (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport_mk_iff U g h).mp hc⟩
    · rintro ⟨h, hh, hc⟩
      change QuotientGroup.mk h = c at hh
      rw [← hh]
      exact (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport_mk_iff U g h).mpr hc)

variable (q : ℕ) [Fact q.Prime] {s : ℕ} (v : Fin s)

theorem activeCosetMap_mem_raw_iff (g : SphericalGU.Spherical.SL3 q) (c : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) :
    Cosets.Spherical.activeCosetMap q v c ∈ AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g) ↔
      c ∈ AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSL3 q) g := by
  induction c using Quotient.inductionOn with
  | h h =>
    change QuotientGroup.mk (SphericalGU.Spherical.activeEmbedding q v h) ∈
      AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g) ↔ _
    rw [AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport_mk_iff, AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport_mk_iff]
    have he := Basis.Spherical.active_doubleCoset_iff q v g⁻¹ h
    rw [map_inv] at he
    exact he

theorem activeRawSupport_mem_orbit (g : SphericalGU.Spherical.SL3 q)
    (c : AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g)) :
    c.val ∈ SphericalGU.Spherical.activeOrbit q v := by
  obtain ⟨u, hu⟩ := MulAction.mem_orbit_iff.mp c.property
  refine ⟨u.val * (SphericalGU.Spherical.activeEmbedding q v g)⁻¹, ?_, hu⟩
  exact (SphericalGU.Spherical.activeSector q v).mul_mem
    ((show SphericalGU.Spherical.integralSplitGU q s ≤ SphericalGU.Spherical.activeSector q v from le_sup_left) u.property)
    ((SphericalGU.Spherical.activeSector q v).inv_mem
      ((show (SphericalGU.Spherical.activeEmbedding q v).range ≤ SphericalGU.Spherical.activeSector q v from le_sup_right) ⟨g, rfl⟩))

def activeRawSupportMap (g : SphericalGU.Spherical.SL3 q)
    (c : AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSL3 q) g) :
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g) :=
  ⟨Cosets.Spherical.activeCosetMap q v c.val, (activeCosetMap_mem_raw_iff q v g c.val).mpr c.property⟩

def activeRawSupportEquiv (g : SphericalGU.Spherical.SL3 q) :
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSL3 q) g ≃
      AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SphericalGU.Spherical.integralSplitGU q s) (SphericalGU.Spherical.activeEmbedding q v g) :=
  Equiv.ofBijective (activeRawSupportMap q v g) ⟨by
    intro c d h
    exact Subtype.ext (Cosets.Spherical.activeCosetMap_injective q v (congrArg Subtype.val h)), by
    intro c
    obtain ⟨b, hb⟩ := (Cosets.Spherical.activeCosetEquiv q v).surjective ⟨c.val, activeRawSupport_mem_orbit q v g c⟩
    have he : Cosets.Spherical.activeCosetMap q v b = c.val := congrArg Subtype.val hb
    exact ⟨⟨b, (activeCosetMap_mem_raw_iff q v g b).mp (he.symm ▸ c.property)⟩, Subtype.ext he⟩⟩

def clearedActiveSupportCosetEquiv (a : Intrinsic.Hecke.ActiveWeight) :
    AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.representative s q (Intrinsic.Hecke.clearedActiveType v a).val) ≃
      Intrinsic.Hecke.activeCosets q a := by
  refine (CosetShift.rawClearedActiveShiftEquiv q v a).trans ?_
  rw [Basis.Spherical.representative_activeType]
  exact (activeRawSupportEquiv q v (Intrinsic.Hecke.activeSLRepresentative q a)).symm.trans
    (rawSupportDoubleCosetEquiv (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a))

end

end OAI.RepresentationTheory.Theta.Geometric.Active.DoubleCosetFibers.Spherical
