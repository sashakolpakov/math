import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RationalRegularityLocal
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Normal Sections In -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalSectionsIn.Construction.NormalSections

/-! Normality of affine section rings from the actual normal stalks.
In particular this applies to the smooth integral schemes in the cube argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIntegrallyClosedIn_functionField
    {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] : IsIntegrallyClosedIn Γ(X, U) X.functionField := by
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨X.germToFunctionField_injective U, ?_⟩
  intro r hr
  have hlocal (x : U) : ∃ a : X.presheaf.stalk x,
      algebraMap _ X.functionField a = r := by
    have := hX x
    let := X.presheaf.algebra_section_stalk x
    have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U x
    exact (isIntegrallyClosed_iff X.functionField).mp (hX x) hr.tower_top
  obtain ⟨s, hs⟩ := RationalRegularityLocal.Construction.RationalRegularity.exists_section (X := X) (U := U)
    (fun _ => r) hlocal
  exact ⟨s, congrFun hs ⟨inferInstance⟩⟩

theorem affine
    {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField).mpr
    (isIntegrallyClosedIn_functionField hX U)

theorem smooth_affine
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  apply affine _ U hU
  intro x
  have := SmoothStalk.Construction.SmoothStalkFactorial.stalk f x
  infer_instance

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalSectionsIn.Construction.NormalSections
