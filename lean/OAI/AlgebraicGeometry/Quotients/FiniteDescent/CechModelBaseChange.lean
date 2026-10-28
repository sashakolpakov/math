import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechAffineBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorExtensionQuasi

/-! # Cech Model Base Change -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange

noncomputable section

/-! A universally valid algebraic model of Cech cohomology remains a model
of the actual geometric Cech complex after affine base change. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.CechBaseChangeMap

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U)

def modelMap :
    ((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex (ComplexShape.up ℕ)).obj D ⟶
      CechBaseTmul.Construction.CechBaseChangeMap.target f ρ M U :=
  ((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫
    CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g h M U

omit h in
theorem modelMap_quasiIso [IsAffine S] [IsAffine T] [M.IsQuasicoherent] [Finite ι]
    (hp : IsPullback f ρ π g)
    (hU : ∀ (q : ℕ) (i : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    (hφ : ∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A],
      QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) : QuasiIso (modelMap f π ρ g hp.w M U φ) := by
  have : QuasiIso (((ModuleCat.extendScalars g.appTop.hom).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) := TensorExtensionQuasi.Construction.TensorExtension.quasiIso g.appTop.hom φ hφ
  have : IsIso (CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g hp.w M U) := CechAffineBaseChange.Construction.CechBaseChangeMap.isIso_of_affine_intersections f π ρ g hp M U hU
  exact quasiIso_comp _ _

end Construction.CechBaseChangeMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange
