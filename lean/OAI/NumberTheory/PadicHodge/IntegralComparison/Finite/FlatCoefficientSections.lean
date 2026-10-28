import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapPureTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Flat Coefficient Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections

noncomputable section

/-! The original iterated direct-image coefficients on an affine ambient
open are the genuine finite projective algebra of the finite flat map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z) (U : Z.Opens)

abbrev quotientRing := Γ(X, i ⁻¹ᵁ U)
abbrev coefficientRing := Γ(Y, f ⁻¹ᵁ (i ⁻¹ᵁ U))

@[instance_reducible] def quotientAlgebra : Algebra Γ(Z, U) (quotientRing i U) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionAlgebra i U

@[instance_reducible] def coefficientAlgebra :
    Algebra (quotientRing i U) (coefficientRing f i U) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionAlgebra f (i ⁻¹ᵁ U)

@[instance_reducible] def ambientAlgebra : Algebra Γ(Z, U) (coefficientRing f i U) :=
  ((f.app (i ⁻¹ᵁ U)).hom.comp (i.app U).hom).toAlgebra

attribute [local instance] quotientAlgebra coefficientAlgebra ambientAlgebra

instance scalarTower : IsScalarTower Γ(Z, U) (quotientRing i U) (coefficientRing f i U) :=
  IsScalarTower.of_algebraMap_eq' rfl

def literalIso :
    (Affine.ModuleExactSections.sections U).obj (Cech.StructurePullbackUnit.coefficients f i) ≅
      ModuleCat.of Γ(Z, U) (coefficientRing f i U) :=
  (show Γ(Cech.StructurePullbackUnit.coefficients f i, U) ≃ₗ[Γ(Z, U)]
      coefficientRing f i U from
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toModuleIso

def chartIso (hU : IsAffineOpen U) :
    (AffineOpen.InternalHom.sections U hU).obj (Cech.StructurePullbackUnit.coefficients f i) ≅
      ModuleCat.of Γ(Z, U) (coefficientRing f i U) :=
  (Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients f i)).symm ≪≫
    literalIso f i U

variable [IsFinite f] [Flat f] [IsClosedImmersion i] [IsLocallyNoetherian X]
  (hU : IsAffineOpen U)

include hU in
omit [Flat f] [IsLocallyNoetherian X] in
theorem finite : Module.Finite (quotientRing i U) (coefficientRing f i U) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_finite f (i ⁻¹ᵁ U) (hU.preimage i)

include hU in
theorem projective : Module.Projective (quotientRing i U) (coefficientRing f i U) := by
  let : Module.Flat (quotientRing i U) (coefficientRing f i U) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_flat f (i ⁻¹ᵁ U) (hU.preimage i)
  let : IsNoetherianRing (quotientRing i U) :=
    IsLocallyNoetherian.component_noetherian ⟨i ⁻¹ᵁ U, hU.preimage i⟩
  let : Module.FinitePresentation (quotientRing i U) (coefficientRing f i U) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatChartModule.Construction.affinePreimageSectionModule_finitePresentation f (i ⁻¹ᵁ U) (hU.preimage i)
  exact Module.Flat.projective_of_finitePresentation

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
