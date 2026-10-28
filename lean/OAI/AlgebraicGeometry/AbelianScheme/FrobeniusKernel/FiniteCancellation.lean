import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteTargetRigidity

/-! # Finite Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation.Construction

noncomputable section

/-!
Finite group-scheme maps can be cancelled when comparing homomorphisms
from a connected reduced geometric group. The proof factors their ratio
through the actual finite kernel and uses finite-target rigidity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X Y Z : Over (Spec (.of K))} [GrpObj X] [GrpObj Y] [GrpObj Z]
variable [IsReduced X.left] [LocallyOfFiniteType X.hom] [PreconnectedSpace X.left]

/-- Cancellation is on group homomorphisms from the connected source;
the finite map itself need not be a monomorphism of schemes. -/
theorem cancel_finite_group_map (f : Y ⟶ Z) [IsMonHom f] [IsFinite f.left]
    (a b : X ⟶ Y) [IsMonHom a] [IsMonHom b] (hab : a ≫ f = b ≫ f) : a = b := by
  let d : X ⟶ Y := a * b⁻¹
  have hd : d ≫ f = 1 := by
    change (a * b⁻¹) ≫ f = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, mul_inv_cancel]
  let l := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f X).symm ⟨d, hd⟩
  let j := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f
  have hj : l ≫ j = d := congrArg Subtype.val
    ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f X).apply_symm_apply ⟨d, hd⟩)
  have hz : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ X) ≫ d = 1 := by
    change (1 : 𝟙_ (Over (Spec (.of K))) ⟶ X) ≫ (a * b⁻¹) = 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.one_comp, MonObj.one_comp, inv_one, mul_one]
  have hlz : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ X) ≫ l = 1 := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hj, hz, MonObj.one_comp]
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite f
  let x₀ : X.left := (1 : 𝟙_ (Over (Spec (.of K))) ⟶ X).left (IsLocalRing.closedPoint K)
  have hl : l = (1 : X ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f) := by
    apply FiniteTargetRigidity.Construction.finiteTargetHom_ext l 1 x₀
    have hpoint := congrArg (fun k : 𝟙_ (Over (Spec (.of K))) ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f =>
      k.left (IsLocalRing.closedPoint K))
      (hlz.trans (MonObj.comp_one (1 : 𝟙_ (Over (Spec (.of K))) ⟶ X)).symm)
    exact hpoint
  have hd' : d = 1 := hj.symm.trans
    ((congrArg (fun k => k ≫ j) hl).trans (MonObj.one_comp j))
  exact mul_inv_eq_one.mp hd'

/-- Pullback of group homomorphisms along an epimorphism and a finite
dual homomorphism is injective on a connected reduced source. -/
theorem polarizationPullback_injective {W : Over (Spec (.of K))}
    (p : W ⟶ X) [Epi p] (d : Y ⟶ Z) [IsMonHom d] [IsFinite d.left]
    (a b : X ⟶ Y) [IsMonHom a] [IsMonHom b]
    (h : p ≫ a ≫ d = p ≫ b ≫ d) : a = b :=
  cancel_finite_group_map d a b ((cancel_epi p).mp h)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation.Construction
