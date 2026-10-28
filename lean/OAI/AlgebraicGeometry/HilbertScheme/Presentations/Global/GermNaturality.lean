import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.StalkEquations

/-! # Germ Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.GermNaturality

noncomputable section

/-! Global-section germs and the stalk maps of scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem global_germ_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (s : Γ(Y, ⊤)) :
    f.stalkMap x (Y.presheaf.Γgerm (f x) s) = X.presheaf.Γgerm x (f.appTop s) := by
  exact f.germ_stalkMap_apply ⊤ x (by trivial) s

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.GermNaturality
