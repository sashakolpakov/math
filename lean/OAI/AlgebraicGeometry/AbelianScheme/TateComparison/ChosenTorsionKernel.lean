import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionBlockSubgroups

/-! # Chosen Torsion Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual IsogenyQuotient chosen kernel on test points is the intersection
of the finite-level Tate-map kernel with the chosen torsion block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S}
  {n : ℕ} (e : PELIsogenies.PELIsogeny P Q n) (m : ℕ) (v : Fin s × Bool)

def Data.SphericalPELAlbaneseData.torsionKernelBlock : Submodule ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ P.abelian.scheme)) m) :=
  (Add.Tate.mapLevel q (P.abelian.mapPoints Q.abelian e.isogeny.hom T).toAdditive m).ker ⊓
    D.torsionBlock h T P m v

def Data.SphericalPELAlbaneseData.chosenTorsionKernelEquiv : D.torsionKernelBlock h T e m v ≃+
    Additive (((Subgroups.PointSubgroup.kernel e.isogeny.hom).inf
      (Subgroups.splitBlock P (D.localCharacter v) m)).atTest T) where
  toFun x := Additive.ofMul ⟨x.val.val.toMul, by
    refine ⟨?_, (D.torsionBlock_mem_iff h T P m v x.val).mp x.property.2⟩
    exact congrArg (fun y : Add.Tate.torsion q (Additive (T ⟶ Q.abelian.scheme)) m => y.val.toMul)
      x.property.1⟩
  invFun y := by
    let z : Add.Tate.torsion q (Additive (T ⟶ P.abelian.scheme)) m :=
      ⟨Additive.ofMul y.toMul.val, by
        apply Additive.toMul.injective
        rw [toMul_nsmul]
        change y.toMul.val ^ (q ^ m) = 1
        exact y.toMul.property.2.1⟩
    refine ⟨z, ?_, (D.torsionBlock_mem_iff h T P m v z).mpr y.toMul.property.2⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    exact y.toMul.property.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
