import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Identity Pushforward Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IdentityPushforwardModule

noncomputable section

/-! Identity pushforward retains the original module sheaf literally. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

theorem object (X : Scheme.{u}) (N : X.Modules) :
    (Scheme.Modules.pushforward (𝟙 X)).obj N = N := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IdentityPushforwardModule
