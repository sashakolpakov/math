import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.StalkKernel
import OAI.AlgebraicGeometry.Comparison.Betti.SurjectiveRingPushout

/-! # Stalk Base Change -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.StalkBaseChange

noncomputable section

section

/-! Actual algebraic and holomorphic stalks of a smooth closed immersion form a ring pushout. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]
  (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

local notation "A" => OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk.algebraicRingCatStalk Y (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
local notation "B" => OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk.algebraicRingCatStalk X p
local notation "S" => OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap.analyticHolomorphicStalk Y (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
local notation "T" => OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p

theorem closedImmersion_stalk_isPushout :
    let _ : Algebra A B := (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p).toAlgebra
    let _ : Algebra A S := (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).toAlgebra
    let _ : Algebra B T := (Analytification.RingedStalk.analytificationRingedStalkMap X p).toAlgebra
    let _ : Algebra S T := (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p).toAlgebra
    let _ : Algebra A T :=
      ((Analytification.RingedStalk.analytificationRingedStalkMap X p).comp (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)).toAlgebra
    let _ : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower A S T :=
      IsScalarTower.of_algebraMap_eq' (Holomorphic.SchemeStalkPullback.analytificationRingedStalkSquare f p).symm
    Algebra.IsPushout A S B T := by
  let : Algebra A B := (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p).toAlgebra
  let : Algebra A S := (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).toAlgebra
  let : Algebra B T := (Analytification.RingedStalk.analytificationRingedStalkMap X p).toAlgebra
  let : Algebra S T := (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p).toAlgebra
  let : Algebra A T :=
    ((Analytification.RingedStalk.analytificationRingedStalkMap X p).comp (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)).toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S T :=
    IsScalarTower.of_algebraMap_eq' (Holomorphic.SchemeStalkPullback.analytificationRingedStalkSquare f p).symm
  exact SurjectiveRingPushout.isPushout_of_surjective_kernel
    (Algebraic.SchemeStalkNormalization.algebraicSchemeStalkPullback_surjective f p)
    (HolomorphicStalk.analyticHolomorphicStalkPullback_surjective f p)
    (StalkKernel.closedImmersion_analyticStalk_kernel f p)

end

/-! The normalized module tensor comparison over the actual stalk square of a smooth closed immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]
  (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

local notation "A" => OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk.algebraicRingCatStalk Y (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
local notation "B" => OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk.algebraicRingCatStalk X p
local notation "S" => OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap.analyticHolomorphicStalk Y (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)
local notation "T" => OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p

theorem closedImmersion_exists_stalkModuleBaseChange
    (M : Type) [AddCommGroup M] [Module B M] :
    let _ : Module A M := Module.compHom M (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)
    let _ : Algebra A S := (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).toAlgebra
    let _ : Algebra B T := (Analytification.RingedStalk.analytificationRingedStalkMap X p).toAlgebra
    let _ : Algebra S T := (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p).toAlgebra
    ∃ E : S ⊗[A] M ≃ₗ[S] T ⊗[B] M,
      ∀ s m, E (s ⊗ₜ[A] m) = Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p s ⊗ₜ[B] m := by
  let : Module A M := Module.compHom M (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)
  let : Algebra A B := (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p).toAlgebra
  let : IsScalarTower A B M := ⟨fun a b m => by
    change (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p a * b) • m =
      Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p a • (b • m)
    exact mul_smul _ _ _⟩
  let : Algebra A S := (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).toAlgebra
  let : Algebra B T := (Analytification.RingedStalk.analytificationRingedStalkMap X p).toAlgebra
  let : Algebra S T := (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p).toAlgebra
  let : Algebra A T :=
    ((Analytification.RingedStalk.analytificationRingedStalkMap X p).comp (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)).toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S T :=
    IsScalarTower.of_algebraMap_eq' (Holomorphic.SchemeStalkPullback.analytificationRingedStalkSquare f p).symm
  let : Algebra.IsPushout A S B T := closedImmersion_stalk_isPushout f p
  exact ⟨(Algebra.IsPushout.cancelBaseChange A S B T M).symm,
    Algebra.IsPushout.cancelBaseChange_symm_tmul A S B T M⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.StalkBaseChange
