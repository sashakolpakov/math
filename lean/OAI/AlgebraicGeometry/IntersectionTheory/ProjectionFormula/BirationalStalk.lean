import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuationBirational
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.ResidueDegree
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! # Birational Stalk -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalStalk

noncomputable section

/-! A birational scheme map is an isomorphism on a stalk above a valuation
ring. All algebra structures are the actual stalk and generic-field maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
  [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (x : X)

include hη

theorem stalkMap_isIso_of_valuation [ValuationRing (Y.presheaf.stalk (f x))] :
    IsIso (f.stalkMap x) := by
  let R := Y.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let K := X.functionField
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra R K :=
    ((Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.comp (algebraMap R Y.functionField)).toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq
    (Divisor.DivisorRestriction.genericFieldMap_stalk f hη x)
  let e : Y.functionField ≃ₐ[R] K :=
    { (asIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)).commRingCatIsoToRingEquiv with
      commutes' := fun _ => rfl }
  let : IsFractionRing R K := IsFractionRing.of_algEquiv e
  let : IsLocalHom (algebraMap R A) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact (ConcreteCategory.isIso_iff_bijective (f.stalkMap x)).mpr
    (ValuationBirational.algebraMap_bijective R A K)

theorem residueDegree_of_valuation [ValuationRing (Y.presheaf.stalk (f x))] :
    f.residueDegree x = 1 := by
  let := stalkMap_isIso_of_valuation f hη x
  exact Stalk.ResidueDegree.residueDegree_of_isIso_stalkMap f x

theorem coheight_of_valuation [ValuationRing (Y.presheaf.stalk (f x))] :
    Order.coheight (f x) = Order.coheight x := by
  let := stalkMap_isIso_of_valuation f hη x
  have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_eq_coe.mp h

theorem stalkMap_isIso_of_dvr [IsDiscreteValuationRing (Y.presheaf.stalk (f x))] :
    IsIso (f.stalkMap x) := stalkMap_isIso_of_valuation f hη x

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalStalk
