import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Homotopy Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyImage.HomotopyImageZero

noncomputable section

/-! A comparison homotopy carries a vanishing source image to a
vanishing cohomology image under the original target operator. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L M N : CochainComplex C ℕ}
  (t : K ⟶ L) (a : L ⟶ N) (b : N ⟶ N) (g : L ⟶ M) (d : M ⟶ N)
  (h : Homotopy (a ≫ b) (g ≫ d)) (hz : t ≫ g = 0)

def homotopy : Homotopy (t ≫ a ≫ b) 0 :=
  (h.compLeft t).trans (Homotopy.ofEq ((Category.assoc t g d).symm.trans
    ((congrArg (fun f => f ≫ d) hz).trans Limits.zero_comp)))

include h hz in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap t i ≫ HomologicalComplex.homologyMap a i ≫
    HomologicalComplex.homologyMap b i = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact ((homotopy t a b g d h hz).homologyMap_eq i).trans (HomologicalComplex.homologyMap_zero K N i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyImage.HomotopyImageZero
