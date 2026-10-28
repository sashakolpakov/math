import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockTower

/-! # Active Level -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveLevel

noncomputable section

/-! The q-killed part of the original higher-level native block is
the original level-one block, with the same point in the abelian scheme.
This identifies the active enumeration space independently of the common
higher multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices

def killedSubgroupEquiv (q : ℕ) {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) : ActiveTorsionChoices.killedSubgroup q G ≃+ ActiveTorsionChoices.killedSubgroup q H where
  toFun x := ⟨e x.val, by
    change q • e x.val = 0
    rw [← map_nsmul, x.property, map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    change q • e.symm y.val = 0
    rw [← map_nsmul, y.property, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)

variable {O : Type} [CommRing O] {S : Scheme} {g q : ℕ} [Fact q.Prime]
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
  (χ : O →+* ℤ_[q]) (T : Over S) (m : ℕ) (hm : 1 ≤ m)

def originalBlockKilledEquiv :
    ActiveTorsionChoices.killedSubgroup q (Additive (PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ m T)) ≃+
      Additive (PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ 1 T) where
  toFun x := Additive.ofMul ⟨x.val.toMul.val,
    (PELModuli.CMPoints.BlockTower.block_membership_lower_iff A ρ χ 1 m hm T x.val.toMul.val).mpr
      ⟨x.val.toMul.property, by
        have h := congrArg (fun y : Additive (PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ m T) => y.toMul.val) x.property
        simpa only [toMul_nsmul, toMul_zero, Subgroup.coe_pow, Subgroup.coe_one, pow_one] using h⟩⟩
  invFun y := ⟨Additive.ofMul (PELModuli.CMPoints.BlockTower.blockLevelInclusion A ρ χ 1 m hm T y.toMul), by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_nsmul, toMul_zero, Subgroup.coe_pow, Subgroup.coe_one]
    change y.toMul.val ^ q = 1
    simpa only [pow_one] using y.toMul.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))

def nativeBlockKilledEquiv :
    ActiveTorsionChoices.killedSubgroup q (Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m)
      (σ.map (j.projector iota hsplit m τ)))) ≃+
        Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (σ.map (j.projector iota hsplit 1 τ))) :=
  (killedSubgroupEquiv q (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockPointsEquiv j iota hsplit A σ m τ T).toAdditive).trans
    ((originalBlockKilledEquiv A σ (j.localCharacter iota τ) T m hm).trans
      (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockPointsEquiv j iota hsplit A σ 1 τ T).toAdditive.symm)

theorem nativeBlockKilledEquiv_inclusion
    (x : ActiveTorsionChoices.killedSubgroup q (Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m)
      (σ.map (j.projector iota hsplit m τ))))) :
    (nativeBlockKilledEquiv A T m hm j iota hsplit σ τ x).toMul ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (σ.map (j.projector iota hsplit 1 τ)) =
        x.val.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) (σ.map (j.projector iota hsplit m τ)) := by
  let y := originalBlockKilledEquiv A σ (j.localCharacter iota τ) T m hm
    (killedSubgroupEquiv q (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockPointsEquiv j iota hsplit A σ m τ T).toAdditive x)
  exact congrArg Subtype.val
    ((AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockPointsEquiv j iota hsplit A σ 1 τ T).apply_symm_apply y.toMul)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveLevel
