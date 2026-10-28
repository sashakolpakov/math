import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite Pushforward -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePushforward.Construction

noncomputable section

/-! Finite pushforward preserves coherent module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem finitePushforward_sections_finite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : Y.affineOpens) :
    Module.Finite Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1) := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  let hM : Module.Finite Γ(X, V.1) Γ(M, V.1) :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M V
  let : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.app U.1).hom.toAlgebra
  let hA : Module.Finite Γ(Y, U.1) Γ(X, V.1) := f.finite_app U.1 U.2
  let : Module Γ(Y, U.1) Γ(M, V.1) := Module.compHom Γ(M, V.1) (f.app U.1).hom
  let hT : IsScalarTower Γ(Y, U.1) Γ(X, V.1) Γ(M, V.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact @Module.Finite.trans Γ(Y, U.1) Γ(X, V.1) Γ(M, V.1) _ _ _ _ _ _ hT hA hM

theorem finitePushforward_isFiniteType {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj M).IsFiniteType := by
  have : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  exact OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_of_sections_module_finite _ (finitePushforward_sections_finite f M)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FinitePushforward.Construction
