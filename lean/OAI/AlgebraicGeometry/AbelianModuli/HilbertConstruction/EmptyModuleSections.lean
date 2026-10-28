import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import Mathlib.Algebra.Category.Grp.Zero

/-! # Empty Module Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyModuleSections

noncomputable section

/-! Sections of a module sheaf on an empty open form a singleton. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem moduleSections_subsingleton_of_empty {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : U = ⊥) : Subsingleton Γ(M, U) := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  exact AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty hU).isZero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyModuleSections
