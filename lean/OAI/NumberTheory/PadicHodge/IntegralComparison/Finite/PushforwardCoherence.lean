import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ScalarRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Pushforward Coherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardCoherence

noncomputable section

/-!
# IntegralComparison: finite scheme pushforward preserves finite-type quasicoherent modules
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]

theorem sections_finite (U : Y.affineOpens) :
    Module.Finite Γ(Y, U.1) Γ((pushforward f).obj M, U.1) := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  let : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M V
  exact ScalarRestriction.finite (f.app U.1).hom (f.finite_app U.1 U.2)
    (ModuleCat.of Γ(X, V.1) Γ(M, V.1))

theorem finiteType : ((pushforward f).obj M).IsFiniteType := by
  let : ((pushforward f).obj M).IsQuasicoherent := OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  exact OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_of_sections_module_finite ((pushforward f).obj M) (sections_finite f M)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardCoherence
