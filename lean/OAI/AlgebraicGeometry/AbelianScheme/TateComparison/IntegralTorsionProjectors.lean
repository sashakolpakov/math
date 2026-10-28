import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralResidues
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TorsionBlockSubgroups

/-! # Integral Torsion Projectors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralTorsionProjectors.SphericalPELAlbaneseData

noncomputable section

/-! The integral residue representatives act as the actual completed
projectors on every q-power torsion group, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Classical BigOperators

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) (n : ℕ)

local instance : Module ℤ_[q] (Add.Tate.torsion q (Additive (T ⟶ F.abelian.scheme)) n) :=
  Add.Tate.torsion_padicModule q (Additive (T ⟶ F.abelian.scheme)) n

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.splitTorsionAction_eq_of_residues (a b : Fin s × Bool → ℤ_[q])
    (hab : ∀ v, PadicInt.toZModPow n (a v) = PadicInt.toZModPow n (b v)) :
    D.splitTorsionAction hg T F n a = D.splitTorsionAction hg T F n b := by
  let θ := D.splitTorsionAction hg T F n
  apply LinearMap.ext
  intro x
  have hsum : ∑ v, ProductActionDecomposition.ProductAction.projector θ v x = x := by
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using
      LinearMap.congr_fun (ProductActionDecomposition.ProductAction.sum_projector θ) x
  calc
    θ a x = ∑ v, θ a (ProductActionDecomposition.ProductAction.projector θ v x) := by
      rw [← map_sum, hsum]
    _ = ∑ v, θ b (ProductActionDecomposition.ProductAction.projector θ v x) := by
      apply Finset.sum_congr rfl
      intro v _
      let y : ProductActionDecomposition.ProductAction.block θ v := ⟨ProductActionDecomposition.ProductAction.projector θ v x, ⟨x, rfl⟩⟩
      change θ a y.val = θ b y.val
      rw [ProductActionDecomposition.ProductAction.action_on_block, ProductActionDecomposition.ProductAction.action_on_block]
      change PadicInt.toZModPow n (a v) • y.val = PadicInt.toZModPow n (b v) • y.val
      rw [hab v]
    _ = θ b x := by rw [← map_sum, hsum]

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.integralResidueProjector_action (v : Fin s × Bool) :
    TorsionAction.torsionIntegralAction T q n F (D.integralResidueProjector n hg v) =
      ProductActionDecomposition.ProductAction.projector (D.splitTorsionAction hg T F n) v := by
  rw [← D.splitTorsionAction_character hg T F n, ProductActionDecomposition.ProductAction.projector_eq_single]
  apply D.splitTorsionAction_eq_of_residues hg T F n
  intro w
  rw [D.integralResidueProjector_residues n hg v w]
  by_cases hw : w = v <;> simp [hw]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralTorsionProjectors.SphericalPELAlbaneseData
