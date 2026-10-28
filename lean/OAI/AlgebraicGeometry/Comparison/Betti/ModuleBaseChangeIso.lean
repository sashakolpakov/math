import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.StalkBaseChange
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Module Base Change Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ModuleBaseChangeIso

noncomputable section

/-! Actual stalk base change as an isomorphism of the native extension and restriction of scalars, normalized on the original tensor units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]
  (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

local notation "A" => OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk.algebraicRingCatStalk Y (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
local notation "B" => OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk.algebraicRingCatStalk X p
local notation "S" => OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap.analyticHolomorphicStalk Y (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
local notation "T" => OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p

theorem closedImmersion_exists_stalkModuleBaseChangeIso (M : ModuleCat.{0} B) :
    ∃ E : (ModuleCat.extendScalars (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).obj
        ((ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)).obj M) ≅
      (ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)).obj
        ((ModuleCat.extendScalars (Analytification.RingedStalk.analytificationRingedStalkMap X p)).obj M),
      ∀ m : M, E.hom
        ((ModuleCat.extendRestrictScalarsAdj
          (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).unit.app _ m) =
        (ModuleCat.extendRestrictScalarsAdj (Analytification.RingedStalk.analytificationRingedStalkMap X p)).unit.app M m := by
  let : Module A M := Module.compHom M (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)
  let : Algebra A S := (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).toAlgebra
  let : Algebra B T := (Analytification.RingedStalk.analytificationRingedStalkMap X p).toAlgebra
  let : Algebra S T := (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p).toAlgebra
  obtain ⟨e, he⟩ := ClosedImmersion.StalkBaseChange.closedImmersion_exists_stalkModuleBaseChange f p M
  let E : (ModuleCat.extendScalars (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).obj
      ((ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)).obj M) ≅
    (ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)).obj
      ((ModuleCat.extendScalars (Analytification.RingedStalk.analytificationRingedStalkMap X p)).obj M) :=
    LinearEquiv.toModuleIso e
  refine ⟨E, fun m => ?_⟩
  change e ((1 : S) ⊗ₜ[A] m) = (1 : T) ⊗ₜ[B] m
  exact (he 1 m).trans (congrArg (fun t : T => t ⊗ₜ[B] m)
    (map_one (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ModuleBaseChangeIso
