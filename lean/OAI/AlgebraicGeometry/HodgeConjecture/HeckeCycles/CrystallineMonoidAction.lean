import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms

/-! # Crystalline Monoid Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction.CM.End

noncomputable section

/-! The actual big crystalline H1 pullbacks form an opposite ring action
once the group-law identity has been proved. This module isolates the
formal consequence; the group-law identity is not asserted or installed
as a source hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM

variable (q : ℕ) [Fact q.Prime]

variable (A : Over (Spec (.of (ZMod q)))) [GrpObj A] [IsCommMonObj A]

def monoidAction : (FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)ᵐᵒᵖ →* Module.End ℚ_[q] (NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.RationalH1 q A) where
  toFun f := NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q f.unop.toMul.hom.hom
  map_one' := CrystallineFunctoriality.CM.rationalPullback_id q A
  map_mul' f g := by
    change NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (g.unop * f.unop).toMul.hom.hom = _
    rw [FormalGeometry.Completion.Endomorphisms.Construction.algebraicEnd_mul_apply, ← CrystallineFunctoriality.CM.rationalPullback_comp]
    rfl

def GroupLawIdentity : Prop :=
  NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q μ[A] =
    NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (fst A A) + NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (snd A A)

omit [IsCommMonObj A] in
theorem pullback_mul_of_groupLaw (h : GroupLawIdentity q A)
    {X : Over (Spec (.of (ZMod q)))} (f g : X ⟶ A) :
    NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (f * g) = NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q f + NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q g := by
  change NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q (lift f g ≫ μ[A]) = _
  rw [← CrystallineFunctoriality.CM.rationalPullback_comp, show NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q μ[A] = _ from h,
    LinearMap.comp_add, CrystallineFunctoriality.CM.rationalPullback_comp, CrystallineFunctoriality.CM.rationalPullback_comp, lift_fst, lift_snd]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineMonoidAction.CM.End
