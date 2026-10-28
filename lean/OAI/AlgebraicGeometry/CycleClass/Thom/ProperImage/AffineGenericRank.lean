import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.ResidueDegree
import Mathlib.LinearAlgebra.Dimension.Localization

/-! # Affine Generic Rank -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineGenericRank.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} [IsIntegral S] [IsIntegral T]

/-- Generic-field pullback agrees with the pullback on any pair of
affine neighborhoods of the generic points. -/
theorem genericFieldMap_germ_appLE
    (i : S ⟶ T) (hη : i (genericPoint S) = genericPoint T)
    (U : T.Opens) (V : S.Opens) (hVU : V ≤ i ⁻¹ᵁ U)
    (hηU : genericPoint T ∈ U) (hηV : genericPoint S ∈ V) :
    T.presheaf.germ U (genericPoint T) hηU ≫ FunctionFields.Constructions.Construction.genericFieldMap i hη =
      i.appLE U V hVU ≫ S.presheaf.germ V (genericPoint S) hηV := by
  simp only [FunctionFields.Constructions.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  have h := T.presheaf.germ_stalkSpecializes hηU (Inseparable.of_eq hη).specializes
  have hfirst := (congrArg
    (fun k : Γ(T, U) ⟶ T.presheaf.stalk (i (genericPoint S)) =>
      k ≫ i.stalkMap (genericPoint S)) h).trans
      (i.germ_stalkMap U (genericPoint S) (hVU hηV))
  exact hfirst.trans (by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res])

/-- The residue degree at the generic point is the rank of the actual
pullback between any two nonempty affine neighborhoods. -/
theorem residueDegree_eq_affine_rank
    (i : S ⟶ T) (hη : i (genericPoint S) = genericPoint T)
    (U : T.Opens) (V : S.Opens) (hVU : V ≤ i ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hηU : genericPoint T ∈ U) (hηV : genericPoint S ∈ V) :
    i.residueDegree (genericPoint S) =
      @Module.finrank Γ(T, U) Γ(S, V) _ _ (i.appLE U V hVU).hom.toAlgebra.toModule := by
  let : Nonempty U := ⟨⟨genericPoint T, hηU⟩⟩
  let : Nonempty V := ⟨⟨genericPoint S, hηV⟩⟩
  let := (i.appLE U V hVU).hom.toAlgebra
  let := (FunctionFields.Constructions.Construction.genericFieldMap i hη).hom.toAlgebra
  let : Algebra Γ(T, U) S.functionField :=
    ((S.germToFunctionField V).hom.comp (i.appLE U V hVU).hom).toAlgebra
  let : IsScalarTower Γ(T, U) Γ(S, V) S.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Γ(T, U) T.functionField S.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (genericFieldMap_germ_appLE i hη U V hVU hηU hηV)).symm
  let : IsFractionRing Γ(T, U) T.functionField :=
    functionField_isFractionRing_of_isAffineOpen T U hU
  let : IsFractionRing Γ(S, V) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S V hV
  exact (ResidueDegree.Constructions.Construction.genericFieldMap_finrank_eq_residueDegree i hη).symm.trans
    (IsFractionRing.finrank_eq Γ(T, U) T.functionField Γ(S, V) S.functionField)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AffineGenericRank.Constructions.Construction
