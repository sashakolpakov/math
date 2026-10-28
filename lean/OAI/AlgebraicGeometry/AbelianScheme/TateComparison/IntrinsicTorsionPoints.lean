import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups

/-! # Intrinsic Torsion Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicTorsionPoints

noncomputable section

/-! The finite torsion groups defining the Tate module are the actual
points of the native torsion schemes, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (T : Over S) (q : ℕ) [Fact q.Prime] (n : ℕ)

private instance power_isMonHom : IsMonHom ((𝟙 A) ^ (q ^ n)) :=
  Picard.PoincareBundle.Epi.Construction.isMonHom_pow (𝟙 A) (q ^ n)

private instance multiplicationKernel_group : GrpObj (Picard.PoincareBundle.Kernel.Scheme.kernelObject ((𝟙 A) ^ (q ^ n))) :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup ((𝟙 A) ^ (q ^ n))

def torsionKernelPointEquiv : Add.Tate.torsion q (Additive (T ⟶ A)) n ≃+
    Additive (Picard.PoincareBundle.Kernel.Scheme.pointsMap ((𝟙 A) ^ (q ^ n)) T).ker where
  toFun x := Additive.ofMul ⟨x.val.toMul, by
    change x.val.toMul ≫ (𝟙 A) ^ (q ^ n) = 1
    rw [MonObj.comp_pow, Category.comp_id]
    exact x.property⟩
  invFun x := ⟨Additive.ofMul x.toMul.val, by
    have h := x.toMul.property
    change x.toMul.val ≫ (𝟙 A) ^ (q ^ n) = 1 at h
    rw [MonObj.comp_pow, Category.comp_id] at h
    exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def nativeTorsionPointEquiv : Add.Tate.torsion q (Additive (T ⟶ A)) n ≃+
    Additive (T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n)) :=
  (torsionKernelPointEquiv A T q n).trans
    (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv ((𝟙 A) ^ (q ^ n)) T).symm.toAdditive

omit [Fact q.Prime] in
theorem nativeTorsionPointEquiv_inclusion (x : Add.Tate.torsion q (Additive (T ⟶ A)) n) :
    (nativeTorsionPointEquiv A T q n x).toMul ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A (q ^ n) =
      x.val.toMul :=
  IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A (q ^ n) x.val.toMul x.property

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicTorsionPoints
