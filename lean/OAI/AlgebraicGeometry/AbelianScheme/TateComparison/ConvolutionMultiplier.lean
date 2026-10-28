import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeNeighbor
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarCosetExponents

/-! # Convolution Multiplier -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionMultiplier

noncomputable section

/-! The ordinary raw convolution coefficients are supported exactly
at the cumulative multiplier of the two source operators. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

theorem mem_sphericalLatticeNeighbors_iff (t : Local.IntegralType s) (x y : LatticeCosetConvolution.SplitLatticePoint s q) :
    y ∈ LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x ↔ LatticeNeighbor.LatticeNeighborRelation s q t x y := by
  rw [← Multiset.count_pos, LatticeNeighbor.sphericalLatticeNeighbors_count]
  by_cases h : LatticeNeighbor.LatticeNeighborRelation s q t x y <;> simp [h]

theorem latticeNeighborRelation_multiplier_comp (u v w : Local.IntegralType s)
    (x y z : LatticeCosetConvolution.SplitLatticePoint s q)
    (hu : LatticeNeighbor.LatticeNeighborRelation s q u x y) (hv : LatticeNeighbor.LatticeNeighborRelation s q v y z)
    (hw : LatticeNeighbor.LatticeNeighborRelation s q w x z) : w.val.multiplier = u.val.multiplier + v.val.multiplier := by
  have h : (QuotientGroup.mk (HeckeKernel.qUnit q ^ (-w.val.multiplier)) : ℚ_[q]ˣ ⧸ SplitCosetComponents.scalarIntegralLevel q) =
      QuotientGroup.mk (HeckeKernel.qUnit q ^ (-(u.val.multiplier + v.val.multiplier))) := by
    calc
      _ = x.2⁻¹ * z.2 := hw.2.symm
      _ = (x.2⁻¹ * y.2) * (y.2⁻¹ * z.2) := by
        exact ((mul_assoc (x.2⁻¹) y.2 (y.2⁻¹ * z.2)).trans
          (congrArg (fun t => x.2⁻¹ * t) (mul_inv_cancel_left y.2 z.2))).symm
      _ = QuotientGroup.mk (HeckeKernel.qUnit q ^ (-u.val.multiplier)) *
          QuotientGroup.mk (HeckeKernel.qUnit q ^ (-v.val.multiplier)) := congrArg₂ (· * ·) hu.2 hv.2
      _ = _ := by rw [← QuotientGroup.mk_mul, ← zpow_add, neg_add_rev]; congr 2; omega
  exact neg_inj.mp (ScalarCosetExponents.scalarCoset_qUnit_zpow_injective q h)

theorem sphericalLatticeNeighbors_nonempty (t : Local.IntegralType s) :
    ∃ y, y ∈ LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val
      (SplitCosetComponents.splitCosetLatticeEquiv s q (QuotientGroup.mk (1 : HeckeKernel.SplitGroup s q))) := by
  let z : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q := QuotientGroup.mk (HeckeKernel.representative s q t.val)⁻¹
  refine ⟨SplitCosetComponents.splitCosetLatticeEquiv s q z, (mem_sphericalLatticeNeighbors_iff s q t _ _).mpr ?_⟩
  apply (LatticeNeighbor.splitRaw_translated_iff_neighborRelation s q t 1 z).mp
  change (1 : HeckeKernel.SplitGroup s q)⁻¹ • z ∈ HeckeKernel.doubleCosetOrbit (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t.val)
  rw [inv_one, one_smul]
  exact ⟨1, by simp [z]⟩

theorem convolutionCoefficients_multiplier (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (u v w : Local.IntegralType s) (hw : ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v w ≠ 0) :
    w.val.multiplier = u.val.multiplier + v.val.multiplier := by
  let x := SplitCosetComponents.splitCosetLatticeEquiv s q (QuotientGroup.mk (1 : HeckeKernel.SplitGroup s q))
  obtain ⟨z, hz⟩ := sphericalLatticeNeighbors_nonempty s q w
  have hn : z ∈ ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v w • LatticeCosetConvolution.sphericalLatticeNeighbors s q w.val x := by
    simp only [Multiset.mem_nsmul]
    exact ⟨hw, hz⟩
  have hle : ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v w • LatticeCosetConvolution.sphericalLatticeNeighbors s q w.val x ≤
      (ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v).sum (fun a n => n • LatticeCosetConvolution.sphericalLatticeNeighbors s q a.val x) :=
    Finset.single_le_sum (f := fun a => ConvolutionCoefficients.convolutionCoefficients s q hElementaryDivisors u v a •
      LatticeCosetConvolution.sphericalLatticeNeighbors s q a.val x) (fun _ _ => zero_le) (Finsupp.mem_support_iff.mpr hw)
  have hmem := Multiset.mem_of_le hle hn
  rw [← LatticeCosetConvolution.sphericalLatticeNeighbors_convolution s q hElementaryDivisors u v x] at hmem
  obtain ⟨y, hy, hyz⟩ := Multiset.mem_bind.mp hmem
  exact latticeNeighborRelation_multiplier_comp s q u v w x y z
    ((mem_sphericalLatticeNeighbors_iff s q u x y).mp hy)
    ((mem_sphericalLatticeNeighbors_iff s q v y z).mp hyz)
    ((mem_sphericalLatticeNeighbors_iff s q w x z).mp hz)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConvolutionMultiplier
