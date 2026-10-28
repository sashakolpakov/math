import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitTorsionBlocks

/-! # Torsion Block Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The torsion projector range equals the original IsogenyQuotient split subgroup
on actual test-scheme points, with its literal residue-scalar equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem TorsionBlockSubgroups.Tate.padic_smul_val (q : ℕ) [Fact q.Prime] {H : Type u} [AddCommGroup H]
    (n : ℕ) (z : ℤ_[q]) (x : Add.Tate.torsion q H n) :
    (z • x).val = (PadicInt.toZModPow n z).val • x.val := by
  change (PadicInt.toZModPow n z • x).val = _
  conv_lhs => rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n z)]
  rw [Nat.cast_smul_eq_nsmul]
  rfl

theorem TorsionBlockSubgroups.torsionIntegralAction_point {R : Type u} [CommRing R] {S : Scheme.{u}}
    {g N : ℕ} (T : Over S) (q : ℕ) [Fact q.Prime] (n : ℕ)
    (F : PEL.PELFamilyData R g N S) (r : R)
    (x : Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :
    (TorsionAction.torsionIntegralAction T q n F r x).val.toMul =
      x.val.toMul ≫ End.endSchemeMap F.abelian.scheme (F.action r) :=
  End.endSchemeMap_points F.abelian.scheme (F.action r) T x.val.toMul

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (n : ℕ)

theorem Data.SphericalPELAlbaneseData.torsionBlock_mem_iff (v : Fin s × Bool)
    (x : Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :
    x ∈ D.torsionBlock h T F n v ↔
      x.val.toMul ∈ (Subgroups.splitBlock F (D.localCharacter v) n).atTest T := by
  change x ∈ ProductActionDecomposition.ProductAction.block (D.splitTorsionAction h T F n) v ↔ _
  rw [D.block_mem_iff_characters h]
  simp_rw [D.splitTorsionAction_character h T F n]
  have hp : x.val.toMul ^ (q ^ n) = 1 := by
    have hx := congrArg Additive.toMul x.property
    simpa using hx
  constructor
  · intro hx
    refine ⟨hp, ?_⟩
    intro r
    have he := congrArg (fun y : Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n => y.val.toMul) (hx r)
    rw [TorsionBlockSubgroups.torsionIntegralAction_point, TorsionBlockSubgroups.Tate.padic_smul_val, toMul_nsmul] at he
    exact he
  · intro hx r
    apply Subtype.ext
    apply Additive.toMul.injective
    rw [TorsionBlockSubgroups.torsionIntegralAction_point, TorsionBlockSubgroups.Tate.padic_smul_val, toMul_nsmul]
    exact hx.2 r

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
