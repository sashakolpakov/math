import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartCoefficientSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GlobalFunctionDimension

/-! # Global Function Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalFunctionDimension

noncomputable section

/-! The pointed proper smooth connectedness criterion can be stated over the actual coefficient field, using global regular functions with their structural algebra action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

theorem coefficientSectionMap_top {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : R →+* Γ(X, ⊤)) : AlgebraPresheaf.coefficientSectionMap f ⊤ = f := by
  change (X.presheaf.map (𝟙 (op ⊤))).hom.comp f = f
  rw [X.presheaf.map_id]
  rfl

theorem schemeGlobalCoefficient_bijective_iff {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) : Function.Bijective (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ↔ Function.Bijective p.appTop.hom :=
  Function.Bijective.of_comp_iff p.appTop.hom
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective

def coefficientGlobalFunctionDimension {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) : ℕ :=
  Module.finrank R (AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤)

theorem coefficientGlobalFunctionDimension_eq_one_iff_iso
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) :
    coefficientGlobalFunctionDimension p = 1 ↔ IsIso p.appTop := by
  have hd : coefficientGlobalFunctionDimension p = 1 ↔
      Function.Bijective (AlgebraPresheaf.coefficientSectionMap (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap
  rw [coefficientSectionMap_top] at hd
  have h := hd.trans (schemeGlobalCoefficient_bijective_iff p)
  constructor
  · intro hn
    exact (RingEquiv.ofBijective p.appTop.hom (h.mp hn)).toCommRingCatIso.isIso_hom
  · intro hi
    let : IsIso p.appTop := hi
    exact h.mpr (ConcreteCategory.bijective_of_isIso p.appTop)

theorem pointed_coefficientGlobalFunctionDimension_pos
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [Module.Finite K (AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤)]
    (x : Spec (.of K) ⟶ X) : 0 < coefficientGlobalFunctionDimension p := by
  let : Nontrivial Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).hom.hom.domain_nontrivial
  let : Nontrivial (AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤) := x.appTop.hom.domain_nontrivial
  exact Module.finrank_pos

theorem properSmoothPointed_connected_iff_coefficient_dimension_le_one
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p] [Smooth p]
    [Module.Finite K (AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤)]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _) :
    GeometricallyConnected p ↔ coefficientGlobalFunctionDimension p ≤ 1 := by
  have h := (HilbertConstruction.Field.GlobalFunctionsConnectedness.properSmoothPointed_geometricallyConnected_iff_globalFunctionsIso p x hx).trans
    (coefficientGlobalFunctionDimension_eq_one_iff_iso p).symm
  have hp := pointed_coefficientGlobalFunctionDimension_pos p x
  exact h.trans (by omega)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalFunctionDimension
