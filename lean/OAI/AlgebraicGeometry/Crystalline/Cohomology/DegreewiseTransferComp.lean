import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Degreewise Transfer Comp -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DegreewiseTransferComp.DegreewiseTransfer

noncomputable section

/-!
# Assembling a degreewise transfer

An injective chain map detects compatibility with the differential.
Thus a degreewise transfer whose composite is a scalar multiple of a
known chain map is itself a chain map.
-/

open _root_.CategoryTheory

universe u v

variable (R : Type u) [CommRing R]
  (C : CochainComplex (ModuleCat.{v} R) ℕ) (F P : C ⟶ C)
  (t : ∀ n, C.X n ⟶ C.X n) (c : R)
  (hF : ∀ n, Mono (F.f n)) (ht : ∀ n, t n ≫ F.f n = c • P.f n)

def chain : C ⟶ C where
  f := t
  comm' i j _ := by
    let := hF j
    apply (cancel_mono (F.f j)).mp
    calc
      (t i ≫ C.d i j) ≫ F.f j = t i ≫ F.f i ≫ C.d i j := by
        rw [Category.assoc, ← F.comm i j]
      _ = (c • P.f i) ≫ C.d i j := by rw [← Category.assoc, ht i]
      _ = c • (C.d i j ≫ P.f j) := by rw [Linear.smul_comp, P.comm i j]
      _ = C.d i j ≫ (c • P.f j) := (Linear.comp_smul _ _ _ _ _ _).symm
      _ = (C.d i j ≫ t j) ≫ F.f j := by rw [← ht j, Category.assoc]

theorem chain_comp : chain R C F P t c hF ht ≫ F = c • P := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ht n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DegreewiseTransferComp.DegreewiseTransfer
