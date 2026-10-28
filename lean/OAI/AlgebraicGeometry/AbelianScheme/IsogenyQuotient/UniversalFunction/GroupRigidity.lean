import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Products
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.GroupRigidity

/-! # Group Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.GroupRigidity.Construction

noncomputable section

/-! Universal global functions identify pointed maps and Picard group
structures without a Noetherian hypothesis on the base or test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem pointed_isMonHom_of_universal_functions
    {S : Scheme.{u}} (A B : Over S) [groupA : GrpObj A] [commA : IsCommMonObj A] [groupB : GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A) (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f :=
  Relative.GroupRigidity.Construction.pointed_isMonHom_of_square_functions A B (hA.product hA).restrict f hf

theorem groupStructure_eq_of_origin_of_universal_functions
    {S : Scheme.{u}} (X : Over S) (G H : GrpObj X) (hcomm : letI := G; IsCommMonObj X)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (hX : GlobalFunctions.Construction.HasUniversalGlobalFunctions X) (hunit : G.toMonObj.one = H.toMonObj.one) : G = H := by
  have h := pointed_isMonHom_of_universal_functions (groupA := G) (commA := hcomm) (groupB := H)
    X X hX (𝟙 X) ((Category.comp_id G.toMonObj.one).trans hunit)
  have hm := @IsMonHom.mul_hom _ _ _ _ _ G.toMonObj H.toMonObj (𝟙 X) h
  have hmul : G.toMonObj.mul = H.toMonObj.mul := by
    simpa only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp] using hm
  exact GrpObj.ext G H (Picard.Homomorphisms.DualGroupComparison.Construction.monObj_eq_of_operations G.toMonObj H.toMonObj hunit hmul)

theorem dualPicardGroup_eq_given_of_universal_functions
    {S : Scheme.{u}} {A : Over S} [GrpObj A]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (hD : GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian) :
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D = D.group :=
  groupStructure_eq_of_origin_of_universal_functions D.abelian _ _
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) hD
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_origin D)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.GroupRigidity.Construction
