import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricKernelChoices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIntegralBlocks
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockTateChoices

/-! # Geometric Branches -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual IsogenyQuotient branches over every geometric point correspond to the
raw local right-coset supports. The rank-three bases are constructed on
the actual Tate blocks, and the subgroup formula is the actual kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) (h : D.HasIntegralModelGeometry)
  {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

def Data.SphericalPELAlbaneseData.geometricIntegralBlockBasis (v : Fin s × Bool) :
    Module.Basis (Fin 3) ℤ_[q]
      (D.integralTateBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) v) := by
  have hff := D.fiberTateBlock_finite_free b x hg v
  have := hff.1
  have := hff.2
  exact Module.finBasisOfFinrankEq ℤ_[q] _
    (D.geometricIntegralBlock_finrank hg hdegree hs h b x v)

def Data.SphericalPELAlbaneseData.geometricRawBlockSubgroupEquiv (t : Local.IntegralType s) (v : Fin s) :
    IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
        (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => (t.exponentNat v i : ℤ))) ≃
      {J : AddSubgroup (D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k))))
          (D.fiberFamily b x) t.multiplierNat (v, false)) //
        Nonempty (J ≃+ (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)))} := by
  have : CharZero k := FiberLattices.charZero_of_field_spec_map b
  exact IsogenyQuotient.BlockTateChoices.Construction.rawTateBlockSubgroupChoicesEquiv q t.multiplierNat
    (D.splitTateAction hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x))
    (D.splitTorsionAction hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) t.multiplierNat)
    (D.evaluate_splitAction hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) t.multiplierNat)
    (GeometricDivision.geometricPoint_divisible (D.fiberFamily b x).abelian q) (v, false)
    (D.geometricIntegralBlockBasis hg hdegree hs h b x (v, false))
    (t.exponentNat v) (t.exponentNat_le v)
    (fun _ _ hij => Int.toNat_le_toNat (t.val.dominant v hij)) IsogenyQuotient.ElementaryDivisors.Construction.verified_ElementaryDivisorsInput

def Data.SphericalPELAlbaneseData.geometricFiberRawCosetEquiv (hIsogenyQuotient : D.RealizesIsogenyQuotient) (t : Local.IntegralType s) :
    (D.correspondence t).Fiber x ≃
      ∀ v : Fin s, IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
        (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => (t.exponentNat v i : ℤ))) :=
  (D.c46FiberTorsionSubgroupEquiv t hg b hIsogenyQuotient x).trans
    (Equiv.piCongrRight fun v => (D.geometricRawBlockSubgroupEquiv hg hdegree hs h b x t v).symm)

theorem Data.SphericalPELAlbaneseData.geometricFiberRawCosetEquiv_kernel (hIsogenyQuotient : D.RealizesIsogenyQuotient) (t : Local.IntegralType s)
    (c : (D.correspondence t).Fiber x) (v : Fin s)
    (z : D.torsionBlock hg (Over.mk (𝟙 (Spec (.of k)))) (D.fiberFamily b x) t.multiplierNat (v, false)) :
    z ∈ (D.geometricRawBlockSubgroupEquiv hg hdegree hs h b x t v
      (D.geometricFiberRawCosetEquiv hg hdegree hs h b x hIsogenyQuotient t c v)).val ↔
      z.val.val.toMul ≫
        (D.c46FiberIsogeny hIsogenyQuotient t x (c.val ≫ (D.correspondence t).target)
          c.val c.property rfl).isogeny.hom = 1 := by
  change z ∈ (D.geometricRawBlockSubgroupEquiv hg hdegree hs h b x t v
    ((D.geometricRawBlockSubgroupEquiv hg hdegree hs h b x t v).symm
      (D.c46FiberTorsionSubgroupEquiv t hg b hIsogenyQuotient x c v))).val ↔ _
  rw [Equiv.apply_symm_apply]
  exact D.c46FiberTorsionSubgroupEquiv_membership t hg b hIsogenyQuotient x c v z

include hg hdegree hs h in
theorem Data.SphericalPELAlbaneseData.geometricBranchCount (hIsogenyQuotient : D.RealizesIsogenyQuotient) (t : Local.IntegralType s) :
    Nat.card ((D.correspondence t).Fiber x) =
      ∏ v : Fin s, Nat.card (IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
        (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => (t.exponentNat v i : ℤ)))) := by
  rw [Nat.card_congr (D.geometricFiberRawCosetEquiv hg hdegree hs h b x hIsogenyQuotient t), Nat.card_pi]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
