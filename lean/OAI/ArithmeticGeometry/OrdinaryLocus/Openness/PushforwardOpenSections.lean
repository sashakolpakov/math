import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections

/-! # Pushforward Open Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections.Construction

noncomputable section

/-! Sections of the pushed-forward structure sheaf are the actual inverse-image coordinate ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def pushforwardUnitOpenSectionsLinearEquiv {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (π : Y ⟶ S) (U : Y.Opens) :
    letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ π) (f ⁻¹ᵁ U)
    (BaseOpenSections.Construction.baseOpenSectionsFunctor π U).obj
      ((Scheme.Modules.pushforward f).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)) ≃ₗ[Γ(S, ⊤)]
      Γ(X, f ⁻¹ᵁ U) :=
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (f ≫ π) (f ⁻¹ᵁ U)
  { toFun := id
    invFun := id
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' r x := by
      change Γ(X, f ⁻¹ᵁ U) at x
      change f.app U (BaseOpenSections.Construction.baseOpenScalarMap π U r) * x =
        BaseOpenSections.Construction.baseOpenScalarMap (f ≫ π) (f ⁻¹ᵁ U) r * x
      exact congrArg (fun a => a * x) (RingHom.congr_fun (BaseOpenSections.Construction.baseOpenScalarMap_pullback f π U) r) }

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardOpenSections.Construction
