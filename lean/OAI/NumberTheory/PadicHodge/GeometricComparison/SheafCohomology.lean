import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Sheaf Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCohomology.SheafCohomologyScalars

noncomputable section

/-! Integer multiples commute with maps on actual additive sheaf cohomology. -/

open _root_.CategoryTheory

universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {F G : Sheaf J AddCommGrpCat.{w}}

theorem map_nsmul (f : F ⟶ G) (n N : ℕ) (x : F.H n) :
    Sheaf.H.map (N • f) n x = Sheaf.H.map f n (N • x) := by
  induction N with
  | zero => simp [Sheaf.H.map_apply]
  | succ N ih =>
    rw [succ_nsmul, Sheaf.H.map_add_apply, ih, succ_nsmul, map_add]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCohomology.SheafCohomologyScalars
