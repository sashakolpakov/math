import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

/-! # Split Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitAction.SphericalPELAlbaneseData

noncomputable section

/-! The good-prime completion is a p-adic algebra isomorphism. It
transports the actual completed Tate action to the split product ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.localCompletionMapZq :
    ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E →ₐ[ℤ_[q]] (Fin s × Bool → ℤ_[q]) :=
  AlgHom.liftEquiv ℤ ℤ_[q] (NumberField.RingOfIntegers E) _
    (RingHom.pi D.localCharacter).toIntAlgHom

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.localCompletionMapZq_apply (z : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) :
    D.localCompletionMapZq z = D.localCompletionMap z := by
  induction z using TensorProduct.inductionOn with
  | tmul a r => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.localCompletionEquivZq (h : D.IsGoodCompletelySplitPrime) :
    ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E ≃ₐ[ℤ_[q]] (Fin s × Bool → ℤ_[q]) :=
  AlgEquiv.ofBijective D.localCompletionMapZq
    (by simpa only [Function.Bijective, Function.Injective, Function.Surjective,
      Data.SphericalPELAlbaneseData.localCompletionMapZq_apply] using h.1)

local instance {S : Scheme} (T : Over S)
    (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) :
    Module ℤ_[q] (Add.schemeTateModule F.abelian.scheme T q) :=
  inferInstanceAs (Module ℤ_[q] (Add.Tate.compatible (H := Additive (T ⟶ F.abelian.scheme)) q))

def _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.splitTateAction (h : D.IsGoodCompletelySplitPrime) {S : Scheme}
    (T : Over S) (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S) :
    (Fin s × Bool → ℤ_[q]) →ₐ[ℤ_[q]] Module.End ℤ_[q]
      (Add.schemeTateModule F.abelian.scheme T q) := by
  let M := Add.schemeTateModule F.abelian.scheme T q
  let θ : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E →ₐ[ℤ_[q]] Module.End ℤ_[q] M :=
    TateAction.tateCompletedAction T q F
  let e : (Fin s × Bool → ℤ_[q]) →ₐ[ℤ_[q]] ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E :=
    (D.localCompletionEquivZq h).symm.toAlgHom
  exact θ.comp e

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.splitTateAction_character (h : D.IsGoodCompletelySplitPrime) {S : Scheme}
    (T : Over S) (F : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)
    (r : NumberField.RingOfIntegers E) :
    D.splitTateAction h T F (fun v => D.localCharacter v r) =
      Add.schemeTateMap F.abelian.scheme T q (TateComparison.End.endSchemeMap F.abelian.scheme (F.action r)) := by
  have he : D.localCompletionEquivZq h (1 ⊗ₜ[ℤ] r) = fun v => D.localCharacter v r := by
    change D.localCompletionMapZq (1 ⊗ₜ[ℤ] r) = _
    change (1 : ℤ_[q]) • (fun v => D.localCharacter v r) = _
    exact one_smul _ _
  rw [← he]
  change TateAction.tateCompletedAction T q F
    ((D.localCompletionEquivZq h).symm (D.localCompletionEquivZq h (1 ⊗ₜ[ℤ] r))) = _
  rw [AlgEquiv.symm_apply_apply, TateAction.tateCompletedAction_one_tmul]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitAction.SphericalPELAlbaneseData
