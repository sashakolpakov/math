import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GlobalFunctionsConnectedness
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Global Function Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GlobalFunctionDimension

noncomputable section

/-! The geometric connectedness criterion for a pointed proper smooth field fiber is the numerical condition that its space of global functions has dimension one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def fieldGlobalFunctionDimension {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) : ℕ :=
  Module.finrank Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra p)

theorem fieldGlobalFunctionDimension_eq_one_iff_iso {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) : fieldGlobalFunctionDimension p = 1 ↔ IsIso p.appTop := by
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)).toField
  have h : fieldGlobalFunctionDimension p = 1 ↔ Function.Bijective p.appTop.hom :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap
  constructor
  · intro hn
    exact (RingEquiv.ofBijective p.appTop.hom (h.mp hn)).toCommRingCatIso.isIso_hom
  · intro hi
    let : IsIso p.appTop := hi
    exact h.mpr (ConcreteCategory.bijective_of_isIso p.appTop)

theorem properSmoothPointed_geometricallyConnected_iff_dimension_one
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p] [Smooth p]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) :
    GeometricallyConnected p ↔ fieldGlobalFunctionDimension p = 1 :=
  (GlobalFunctionsConnectedness.properSmoothPointed_geometricallyConnected_iff_globalFunctionsIso p x hx).trans
    (fieldGlobalFunctionDimension_eq_one_iff_iso p).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GlobalFunctionDimension
