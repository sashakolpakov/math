import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Local Fraction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction

noncomputable section

section

/-! Restricting an ambient germ to the function field of a reduced
support is compatible with sections and is independent of the chosen point. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Restriction

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

def toFunctionField (X : Scheme) (W : IrreducibleCloseds X) (x : X) (hx : x ∈ (W : Set X)) :
    X.presheaf.stalk x ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField :=
  Local.Principal.supportStalkMap X W x hx ≫ CommRingCat.ofHom (algebraMap
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx))
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)

theorem germ_square {X Y : Scheme} [IsIntegral Y] (i : Y ⟶ X)
    (U : X.Opens) [Nonempty (i ⁻¹ᵁ U)] (y : Y) (x : X) (h : i y = x) (hxU : x ∈ U) :
    X.presheaf.germ U x hxU ≫ eqToHom (congrArg (fun t => X.presheaf.stalk t) h.symm) ≫
      i.stalkMap y ≫ CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField) =
        i.app U ≫ Y.germToFunctionField (i ⁻¹ᵁ U) := by
  subst x
  simp only [eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, i.germ_stalkMap U y hxU, Category.assoc]
  congr 1
  ext a
  exact Y.algebraMap_germ_eq_germToFunctionField hxU a

theorem toFunctionField_germ (X : Scheme) (W : IrreducibleCloseds X)
    (U : X.Opens) [Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U)]
    (x : X) (hx : x ∈ (W : Set X)) (hxU : x ∈ U) (a : Γ(X, U)) :
    toFunctionField X W x hx (X.presheaf.germ U x hxU a) =
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U)
        ((CycleClass.Geometric.GenericPoint.reducedSupportι W).app U a) :=
  congrArg (fun t : Γ(X, U) ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField => t a)
    (germ_square (CycleClass.Geometric.GenericPoint.reducedSupportι W) U (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx) x (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W x hx) hxU)

theorem germ_independent (X : Scheme) (W : IrreducibleCloseds X) (U : X.Opens)
    (x : X) (hx : x ∈ (W : Set X)) (hxU : x ∈ U)
    (z : X) (hz : z ∈ (W : Set X)) (hzU : z ∈ U) (a : Γ(X, U)) :
    toFunctionField X W x hx (X.presheaf.germ U x hxU a) =
      toFunctionField X W z hz (X.presheaf.germ U z hzU a) := by
  let : Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ U) :=
    ⟨⟨CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx, by
      change CycleClass.Geometric.GenericPoint.reducedSupportι W (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hx) ∈ U
      rwa [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]⟩⟩
  rw [toFunctionField_germ, toFunctionField_germ]

end Restriction

end

/-! A unit at the generic point of a support has, near every point of
that support, a fraction presentation with numerator and denominator
both nonzero on the support. Its restricted rational function is fixed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction.Restriction

theorem exists_fraction (X : Scheme) [IsIntegral X] (W : IrreducibleCloseds X)
    (hz : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ (W : Set X)) (x : X) (hx : x ∈ (W : Set X))
    (u : X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W)) (hu : IsUnit u) :
    ∃ a b : X.presheaf.stalk x,
      Local.Principal.supportStalkMap X W x hx a ≠ 0 ∧ Local.Principal.supportStalkMap X W x hx b ≠ 0 ∧
      algebraMap (X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W)) X.functionField u =
        algebraMap (X.presheaf.stalk x) X.functionField a /
          algebraMap (X.presheaf.stalk x) X.functionField b ∧
      Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hz u =
        Restriction.toFunctionField X W x hx a / Restriction.toFunctionField X W x hx b := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hzU : CycleClass.Thom.IntersectionGeometry.supportPoint W ∈ U :=
    ((W.isIrreducible.isGenericPoint_genericPoint W.isClosed).specializes hx).mem_open U.isOpen hxU
  let B := Γ(X, U)
  let R := X.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint W)
  let : Algebra B R := (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint W) hzU).hom.toAlgebra
  let M := (hU.primeIdealOf ⟨CycleClass.Thom.IntersectionGeometry.supportPoint W, hzU⟩).asIdeal.primeCompl
  let : IsLocalization M R := hU.isLocalization_stalk ⟨CycleClass.Thom.IntersectionGeometry.supportPoint W, hzU⟩
  obtain ⟨⟨c, d⟩, he⟩ := IsLocalization.surj M u
  have hd : IsUnit (algebraMap B R (d : B)) := IsLocalization.map_units R d
  have hc : IsUnit (algebraMap B R c) := he ▸ hu.mul hd
  let a := X.presheaf.germ U x hxU c
  let b := X.presheaf.germ U x hxU (d : B)
  have hγ (v : B) : Restriction.toFunctionField X W x hx (X.presheaf.germ U x hxU v) =
      Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hz (algebraMap B R v) :=
    Restriction.germ_independent X W U x hx hxU (CycleClass.Thom.IntersectionGeometry.supportPoint W) hz hzU v
  have haγ : Restriction.toFunctionField X W x hx a ≠ 0 := by
    rw [hγ c]
    exact (hc.map (Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hz).hom).ne_zero
  have hbγ : Restriction.toFunctionField X W x hx b ≠ 0 := by
    rw [hγ (d : B)]
    exact (hd.map (Restriction.toFunctionField X W (CycleClass.Thom.IntersectionGeometry.supportPoint W) hz).hom).ne_zero
  have ha : Local.Principal.supportStalkMap X W x hx a ≠ 0 := by
    intro h
    apply haγ
    change algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField (Local.Principal.supportStalkMap X W x hx a) = 0
    rw [h, map_zero]
  have hb : Local.Principal.supportStalkMap X W x hx b ≠ 0 := by
    intro h
    apply hbγ
    change algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField (Local.Principal.supportStalkMap X W x hx b) = 0
    rw [h, map_zero]
  have hX (v : B) : algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ U x hxU v) = algebraMap R X.functionField (algebraMap B R v) := by
    change algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hxU v) =
      algebraMap R X.functionField (X.presheaf.germ U (CycleClass.Thom.IntersectionGeometry.supportPoint W) hzU v)
    rw [X.algebraMap_germ_eq_germToFunctionField hxU, X.algebraMap_germ_eq_germToFunctionField hzU]
  have hbX : algebraMap (X.presheaf.stalk x) X.functionField b ≠ 0 := by
    rw [hX (d : B)]
    exact (hd.map (algebraMap R X.functionField)).ne_zero
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · apply (eq_div_iff hbX).mpr
    rw [hX (d : B), hX c, ← map_mul, he]
  · apply (eq_div_iff hbγ).mpr
    rw [hγ (d : B), hγ c, ← map_mul, he]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalFraction
