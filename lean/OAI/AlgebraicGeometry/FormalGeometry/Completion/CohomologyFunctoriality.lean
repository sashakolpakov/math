import OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality

/-! # Cohomology Functoriality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality.Construction

/-!
# Completion: contravariant functoriality of the actual cohomology pullbacks

Both the integral groups and their algebraic coefficient extensions respect
identity and composition of scheme morphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y Z : Scheme.{u}}

/-- Cohomological pullback reverses scheme-morphism composition. -/
theorem integralEllAdicPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (x : Z.EllAdicCohomology ℓ n) :
    ProetalePullback.Construction.integralEllAdicPullback ℓ f n (ProetalePullback.Construction.integralEllAdicPullback ℓ g n x) =
      ProetalePullback.Construction.integralEllAdicPullback ℓ (f ≫ g) n x := by
  change (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ Z).H n at x
  have h := ExtFunctoriality.Construction.ext_transport_comp (ProetalePullback.Construction.proEtSheafPullback g) (ProetalePullback.Construction.proEtSheafPullback f)
    (PullbackCoherence.Construction.proEtSheafPullbackCompIso f g)
    ((ProetalePullback.Construction.proEtConstantPullbackIso g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (ProetalePullback.Construction.proEtCoefficientPullback ℓ g)
    ((ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (ProetalePullback.Construction.proEtCoefficientPullback ℓ f)
    ((ProetalePullback.Construction.proEtConstantPullbackIso (f ≫ g)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (ProetalePullback.Construction.proEtCoefficientPullback ℓ (f ≫ g))
    (ConstantCoherence.Construction.proEtConstantPullbackIso_inv_comp f g (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (PullbackCoherence.Construction.proEtCoefficientPullback_comp ℓ f g).symm x
  simp only [CohomologyPullback.Construction.integralEllAdicPullback_apply]
  exact h

/-- Pullback by the identity scheme morphism is the identity in every degree. -/
theorem integralEllAdicPullback_id (X : Scheme.{u}) (n : ℕ)
    (x : X.EllAdicCohomology ℓ n) : ProetalePullback.Construction.integralEllAdicPullback ℓ (𝟙 X) n x = x := by
  have hc : (ProetalePullback.Construction.proEtConstantPullbackIso (𝟙 X)).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      (PullbackCoherence.Construction.proEtSheafPullbackIdIso X).app (ProetalePullback.Construction.proEtIntegerConstant X) :=
    Iso.ext (ConstantCoherence.Construction.proEtConstantPullbackIso_id X (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  have hi := congrArg Iso.inv hc
  change (ProetalePullback.Construction.proEtConstantPullbackIso (𝟙 X)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
    (PullbackCoherence.Construction.proEtSheafPullbackIdIso X).inv.app (ProetalePullback.Construction.proEtIntegerConstant X) at hi
  change (ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).H n at x
  erw [CohomologyPullback.Construction.integralEllAdicPullback_apply, hi, PullbackCoherence.Construction.proEtCoefficientPullback_id,
    ExtFunctoriality.Construction.ext_mapExactFunctor_iso (ProetalePullback.Construction.proEtSheafPullback (𝟙 X)) (PullbackCoherence.Construction.proEtSheafPullbackIdIso X),
    ExtFunctoriality.Construction.ext_mapExactFunctor_id]

theorem integralEllAdicPullbackLinear_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ f n).comp (CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ g n) =
      CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ (f ≫ g) n := by
  ext x
  exact integralEllAdicPullback_comp ℓ f g n x

theorem integralEllAdicPullbackLinear_id (X : Scheme.{u}) (n : ℕ) :
    CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ (𝟙 X) n = LinearMap.id := by
  ext x
  exact integralEllAdicPullback_id ℓ X n x

/-- The algebraic-coefficient H¹ pullback has the same contravariant order. -/
theorem algebraicEllAdicH1Pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ f).comp (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ g) =
      CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (f ≫ g) := by
  unfold CohomologyPullback.Construction.algebraicEllAdicH1Pullback
  rw [← LinearMap.baseChange_comp, integralEllAdicPullbackLinear_comp]

theorem algebraicEllAdicH1Pullback_id (X : Scheme.{u}) :
    CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ (𝟙 X) = LinearMap.id := by
  unfold CohomologyPullback.Construction.algebraicEllAdicH1Pullback
  rw [integralEllAdicPullbackLinear_id, LinearMap.baseChange_id]

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CohomologyFunctoriality.Construction
