import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveCover

/-! # Trace Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TraceRefinement

noncomputable section

/-! A trace transported between affine covers is compatible with
the literal refinement map, independently of how the trace is constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restore {A B : AddCommGrpCat} (e : A ≅ B) (m : A ⟶ B)
    (h : m = e.hom) {C : Type*} [AddCommGroup C] (t : A →+ C) (x : A) :
    (t.comp e.inv.hom) (m x) = t x := by
  rw [h]
  exact congrArg t (ConcreteCategory.congr_hom e.hom_inv_id x)

universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (M : X.left.Modules) [M.IsQuasicoherent] (i : ℕ) (hi : 0 < i)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R

theorem map_eq_positiveCoverIso :
    (G).map (HomologicalComplex.homologyMap
      (CoverRefinement.map R X U V r M) i) =
    (PositiveCover.Comparison.iso R X U V hU hV haU haV M i hi).hom := by
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ n =>
      exact CoverRefinement.map_eq_coverIso R X U V r M hU hV haU haV n

def transport {C : Type*} [AddCommGroup C]
    (t : (DimensionBound.complex R X M U).homology i →+ C) :
    (DimensionBound.complex R X M V).homology i →+ C :=
  t.comp (PositiveCover.Comparison.iso R X U V hU hV haU haV M i hi).inv.hom

theorem transport_bijective {C : Type*} [AddCommGroup C]
    (t : (DimensionBound.complex R X M U).homology i →+ C)
    (ht : Function.Bijective t) :
    Function.Bijective (transport R X U V hU hV haU haV M i hi t) :=
  ht.comp ((PositiveCover.Comparison.iso R X U V hU hV haU haV M i hi).symm.addCommGroupIsoToAddEquiv.bijective)

abbrev refinement {C : Type*} [AddCommGroup C]
    (t : (DimensionBound.complex R X M U).homology i →+ C)
    (x : (DimensionBound.complex R X M U).homology i) :=
  restore
    (PositiveCover.Comparison.iso R X U V hU hV haU haV M i hi)
    ((G).map (HomologicalComplex.homologyMap
      (CoverRefinement.map R X U V r M) i))
    (map_eq_positiveCoverIso R X U V r hU hV haU haV M i hi) t x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.TraceRefinement
