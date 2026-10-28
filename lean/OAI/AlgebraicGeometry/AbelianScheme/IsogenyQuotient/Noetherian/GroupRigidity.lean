import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.GroupRigidity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GlobalFunctions

/-! # Group Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GroupRigidity.Construction

noncomputable section

/-! The original dual group agrees with its Picard group over
locally Noetherian bases, including nonreduced bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem pointed_isMonHom_over_noetherian_base
    {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [groupA : GrpObj A] [commA : IsCommMonObj A] [groupB : GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f := by
  have : Smooth (A ⊗ A).hom := by dsimp; infer_instance
  have : IsProper (A ⊗ A).hom := by dsimp; infer_instance
  have : GeometricallyConnected (A ⊗ A).hom :=
    GeometricallyConnected.comp (pullback.fst A.hom A.hom) A.hom
  have hσ : η[A ⊗ A].left ≫ (A ⊗ A).hom = 𝟙 S := Over.w η[A ⊗ A]
  apply Relative.GroupRigidity.Construction.pointed_isMonHom_of_square_functions A B ?_ f hf
  intro V
  exact GlobalFunctions.Construction.noetherian_globalFunctions_isIso ((A ⊗ A).hom ∣_ V)
    (AbelianModuli.HilbertConstruction.Family.SectionRestriction.familySectionRestrict (A ⊗ A).hom η[A ⊗ A].left hσ V)
    (AbelianModuli.HilbertConstruction.Family.SectionRestriction.familySectionRestrict_projection (A ⊗ A).hom η[A ⊗ A].left hσ V)

theorem groupStructure_eq_of_origin_over_noetherian_base
    {S : Scheme.{0}} [IsLocallyNoetherian S] (X : Over S)
    (G H : GrpObj X) (hcomm : letI := G; IsCommMonObj X)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (hunit : G.toMonObj.one = H.toMonObj.one) : G = H := by
  have h := pointed_isMonHom_over_noetherian_base (groupA := G) (commA := hcomm) (groupB := H)
    X X (𝟙 X) ((Category.comp_id G.toMonObj.one).trans hunit)
  have hm := @IsMonHom.mul_hom _ _ _ _ _ G.toMonObj H.toMonObj (𝟙 X) h
  have hmul : G.toMonObj.mul = H.toMonObj.mul := by
    simpa only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp] using hm
  exact GrpObj.ext G H (Picard.Homomorphisms.DualGroupComparison.Construction.monObj_eq_of_operations G.toMonObj H.toMonObj hunit hmul)

theorem dualPicardGroup_eq_given_over_noetherian_base
    {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) :
    Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D = D.group :=
  groupStructure_eq_of_origin_over_noetherian_base D.abelian _ _
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D)
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_origin D)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GroupRigidity.Construction
