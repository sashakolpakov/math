import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechGlobalPullbackZero
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOneTensor

/-! # Model Fiber Nonzero -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelFiberNonzero

noncomputable section

/-! A model cycle surviving in a fiber supplies a global section whose
canonical pullback to that fiber is nonzero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe u

namespace Construction.CechBaseChangeMap

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)
variable [QuasiIsoAt φ 0] [QuasiIsoAt (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ) 0]

include h

theorem global_section_pullback_ne_zero (x : (D.d 0 1).hom.ker)
    (hx : (ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g x).val ≠ 0) :
    PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ⊤ (GlobalModel.Construction.GlobalModelSections.equiv π M U hU φ x) ≠ 0 := by
  intro hs
  have hz := CechGlobalPullbackZero.Construction.CechBaseChangeMap.restricted_global_zero f π ρ g h M U (GlobalModel.Construction.GlobalModelSections.equiv π M U hU φ x) hs
  rw [← GlobalModel.Construction.GlobalModelSections.coordinate π M U hU φ x] at hz
  let k := CochainZero.Construction.CochainZeroCycles.kernelEquiv (CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ)
  have he : k (ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g x) = 0 := by
    apply Subtype.ext
    change (k (ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g x)).val = 0
    rw [CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
    exact (ModelOneTensor.Construction.CechBaseChangeMap.model_one f π ρ g h M U φ 0 x.val).trans hz
  have hh : ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g x = 0 := k.injective (he.trans k.map_zero.symm)
  exact hx (congrArg Subtype.val hh)

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelFiberNonzero
