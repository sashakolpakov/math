import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Global Section Dimension -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GlobalSectionDimension.Construction

noncomputable section

/-! Dimension of sections is unchanged by an isomorphism on base functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

universe u

theorem baseGlobalSections_finrank_comp {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ T) [IsIso g.appTop] (M : X.Modules) :
    Module.finrank Γ(T, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ g)).obj M) =
      Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M) := by
  let e : (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ g)).obj M ≃+
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M := AddEquiv.refl _
  have h := rank_eq_of_equiv_equiv (fun r : Γ(T, ⊤) => g.appTop r) e
    (ConcreteCategory.bijective_of_isIso g.appTop) (fun r m => rfl)
  exact congrArg Cardinal.toNat h

theorem baseGlobalSections_finrank_congr {X S : Scheme.{u}} {f g : X ⟶ S}
    (h : f = g) (M : X.Modules) :
    Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M) =
      Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor g).obj M) := by
  subst g
  rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GlobalSectionDimension.Construction
