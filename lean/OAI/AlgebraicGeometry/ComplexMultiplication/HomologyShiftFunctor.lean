import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Homology Shift Functor -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomologyShiftFunctor

noncomputable section

/-! # The actual homology and grading comparison for additive coefficient functors -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit shift of the differential short complex commutes with an additive functor. -/
theorem shiftShortComplexFunctorIso_map (K : CochainComplex C ℤ) (F : C ⥤ D) [F.Additive]
    (n n' : ℤ) (h : 1 + n = n') :
    (HomologicalComplex.shortComplexFunctor D (.up ℤ) n).map
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) ≫
      (CochainComplex.shiftShortComplexFunctorIso D 1 n n' h).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapShortComplex.map ((CochainComplex.shiftShortComplexFunctorIso C 1 n n' h).hom.app K) := by
  subst n'
  ext <;> simp [CochainComplex.shiftShortComplexFunctorIso,
    CochainComplex.shiftShortComplexFunctor', CochainComplex.shiftEval,
    HomologicalComplex.XIsoOfEq, eqToHom_map]
  all_goals
    change (𝟙 _ ≫ eqToHom _) = eqToHom _
    rw [Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The homology comparison respects the actual one-degree shift, including its signs. -/
theorem homologyShiftIso_map (K : CochainComplex C ℤ) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n n' : ℤ) (h : 1 + n = n') :
    (((K⟦(1 : ℤ)⟧).sc n).mapHomologyIso F).hom ≫
      F.map (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n n' h).hom.app K) =
    HomologicalComplex.homologyMap
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) n ≫
      (((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso 1 n n' h).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      ((K.sc n').mapHomologyIso F).hom := by
  change _ ≫ F.map ((CochainComplex.ShiftSequence.shiftIso C 1 n n' h).hom.app K) = _
  rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
  change _ ≫ F.map (ShortComplex.homologyMap
      ((CochainComplex.shiftShortComplexFunctorIso C 1 n n' h).hom.app K)) = _
  rw [← ShortComplex.mapHomologyIso_hom_naturality]
  rw [← shiftShortComplexFunctorIso_map K F n n' h]
  rw [ShortComplex.homologyMap_comp, Category.assoc]
  change _ = HomologicalComplex.homologyMap
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) n ≫
    (CochainComplex.ShiftSequence.shiftIso D 1 n n' h).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ _
  rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomologyShiftFunctor
