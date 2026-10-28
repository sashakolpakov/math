import Mathlib.Algebra.Homology.Homotopy

/-! # Homology Map Precomposition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPrecomposition

/-! Equal maps on original homology remain equal after precomposition. -/

open _root_.CategoryTheory

variable {A : Type*} [Category* A] [Abelian A]
  {K L M : CochainComplex A ℕ} (a : K ⟶ L) (b c : L ⟶ M)

theorem equality (i : ℕ) (h : HomologicalComplex.homologyMap b i = HomologicalComplex.homologyMap c i) :
    HomologicalComplex.homologyMap (a ≫ b) i = HomologicalComplex.homologyMap (a ≫ c) i := by
  let H := HomologicalComplex.homologyFunctor A (.up ℕ) i
  exact (H.map_comp a b).trans ((congrArg (fun t => H.map a ≫ t) h).trans (H.map_comp a c).symm)

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPrecomposition
