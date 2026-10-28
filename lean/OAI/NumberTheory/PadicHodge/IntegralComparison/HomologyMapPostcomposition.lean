import Mathlib.Algebra.Homology.Homotopy

/-! # Homology Map Postcomposition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPostcomposition

/-! Equal maps on original homology remain equal after postcomposition. -/

open _root_.CategoryTheory

variable {A : Type*} [Category* A] [Abelian A]
  {K L M : CochainComplex A ℕ} (a b : K ⟶ L) (c : L ⟶ M)

theorem equality (i : ℕ) (h : HomologicalComplex.homologyMap a i = HomologicalComplex.homologyMap b i) :
    HomologicalComplex.homologyMap (a ≫ c) i = HomologicalComplex.homologyMap (b ≫ c) i := by
  let H := HomologicalComplex.homologyFunctor A (.up ℕ) i
  exact (H.map_comp a c).trans ((congrArg (fun t => t ≫ H.map c) h).trans (H.map_comp b c).symm)

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPostcomposition
