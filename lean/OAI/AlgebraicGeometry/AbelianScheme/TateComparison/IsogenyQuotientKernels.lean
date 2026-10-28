import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ChosenTorsionKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers

/-! # Isogeny Quotient Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual IsogenyQuotient elementary-divisor type is carried to the chosen
finite-level Tate kernel of each constructed geometric fiber isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (h : D.RealizesIsogenyQuotient) {k : Type} [Field k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} (t : Local.IntegralType s)
  (x y : D.GeometricPoint b) (c : Over.mk b ⟶ (D.correspondence t).cover)
  (hs : c ≫ (D.correspondence t).source = x) (ht : c ≫ (D.correspondence t).target = y)
  (v : Fin s)

def Data.SphericalPELAlbaneseData.c46FiberTateKernelEquiv :
    D.torsionKernelBlock hg (Over.mk (𝟙 (Spec (.of k))))
      (D.c46FiberIsogeny h t x y c hs ht) t.multiplierNat (v, false) ≃+
    Additive ((D.chosenKernelAtLift t (D.c46Isogeny h t) x c hs v).atTest
      (Over.mk (𝟙 (Spec (.of k))))) := by
  rw [← D.c46FiberIsogeny_kernel h t x y c hs ht v]
  exact D.chosenTorsionKernelEquiv hg (Over.mk (𝟙 (Spec (.of k))))
    (D.c46FiberIsogeny h t x y c hs ht) t.multiplierNat (v, false)

def Data.SphericalPELAlbaneseData.c46FiberTateKernelType :
    D.torsionKernelBlock hg (Over.mk (𝟙 (Spec (.of k))))
      (D.c46FiberIsogeny h t x y c hs ht) t.multiplierNat (v, false) ≃+
        (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)) := by
  have he := (D.c46FiberKernelChoice h t x ⟨c, hs⟩).property v |>.2.2
  let e := Classical.choice (he k (𝟙 (Spec (.of k))))
  let strip : Additive (Multiplicative (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i))) ≃+
      (∀ i : Fin 3, ZMod (q ^ t.exponentNat v i)) := {
    toFun z := z.toMul.toAdd
    invFun z := Additive.ofMul (Multiplicative.ofAdd z)
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl }
  exact (D.c46FiberTateKernelEquiv hg h t x y c hs ht v).trans (e.toAdditive.trans strip)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
