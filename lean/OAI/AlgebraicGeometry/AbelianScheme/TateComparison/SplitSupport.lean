import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetComponents
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Split Support -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSupport

noncomputable section

/-! Raw split double-coset membership has independent GL3 conditions
and exactly one scalar condition. -/

variable (s q : ℕ) [Fact q.Prime]

theorem split_raw_support_iff (g : HeckeKernel.SplitGroup s q) (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :
    x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) g ↔
      (∀ i, (SplitCosetComponents.splitCosetEquiv s q x).1 i ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) (g.1 i)) ∧
      (SplitCosetComponents.splitCosetEquiv s q x).2 ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SplitCosetComponents.scalarIntegralLevel q) g.2 := by
  induction x using Quotient.inductionOn with
  | h x =>
    change QuotientGroup.mk x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) g ↔
      (∀ i, QuotientGroup.mk (x.1 i) ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) (g.1 i)) ∧
      QuotientGroup.mk x.2 ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SplitCosetComponents.scalarIntegralLevel q) g.2
    simp_rw [IsogenyQuotient.Hecke.Construction.rawRightCosetSupport_mk_iff]
    constructor
    · rintro ⟨k, l, rfl⟩
      have hk := (CentralConvolution.integralLevel_mem_iff s q k.val).mp k.property
      have hl := (CentralConvolution.integralLevel_mem_iff s q l.val).mp l.property
      exact ⟨fun i => ⟨⟨k.val.1 i, hk.1 i⟩, ⟨l.val.1 i, hl.1 i⟩, rfl⟩,
        ⟨⟨k.val.2, hk.2⟩, ⟨l.val.2, hl.2⟩, rfl⟩⟩
    · rintro ⟨hb, a, b, hab⟩
      choose k l hkl using hb
      let k' : HeckeKernel.integralLevel s q := ⟨((fun i => (k i).val), a.val),
        (CentralConvolution.integralLevel_mem_iff s q _).mpr ⟨fun i => (k i).property, a.property⟩⟩
      let l' : HeckeKernel.integralLevel s q := ⟨((fun i => (l i).val), b.val),
        (CentralConvolution.integralLevel_mem_iff s q _).mpr ⟨fun i => (l i).property, b.property⟩⟩
      exact ⟨k', l', Prod.ext (funext hkl) hab⟩

theorem scalar_raw_support_iff (a : ℚ_[q]ˣ) (x : ℚ_[q]ˣ ⧸ SplitCosetComponents.scalarIntegralLevel q) :
    x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (SplitCosetComponents.scalarIntegralLevel q) a ↔ x = QuotientGroup.mk a⁻¹ := by
  change x ∈ HeckeKernel.doubleCosetOrbit (SplitCosetComponents.scalarIntegralLevel q) a ↔ _
  rw [CentralConvolution.doubleCosetOrbit_central (SplitCosetComponents.scalarIntegralLevel q) a (fun b => Commute.all b a)]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSupport
