import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Fields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields
import Mathlib.LinearAlgebra.Dimension.Localization

/-! # Generic Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.GenericDegree

noncomputable section

/-! The rank of a dominant affine chart map is its native generic
residue degree, through the actual scheme function-field maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem rank {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hη : f (genericPoint X) = genericPoint Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = f.residueDegree (genericPoint X) := by
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  let : Algebra R S := (f.app U).hom.toAlgebra
  let : Algebra Y.functionField X.functionField := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let : Algebra R X.functionField := (f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U)).hom.toAlgebra
  let : IsScalarTower R S X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R Y.functionField X.functionField := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (Generic.Fields.genericFieldMap_germ_open f hη U)).symm
  let : IsFractionRing R Y.functionField := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : IsFractionRing S X.functionField := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) hV
  exact (IsFractionRing.finrank_eq R Y.functionField S X.functionField).symm.trans
    (Support.Fields.genericFieldMap_finrank_eq_residueDegree f hη)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.GenericDegree
