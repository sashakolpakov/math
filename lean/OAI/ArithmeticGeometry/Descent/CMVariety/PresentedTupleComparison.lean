import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicEnhancement
import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli

/-! # Presented Tuple Comparison -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Exact recovery of a fixed CM enhancement through actual geometric fiber presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def StandardModuli.Abelian.ComplexAbelianPresentation.transport
    {g : ℕ} {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (P : StandardModuli.Abelian.ComplexAbelianPresentation B) :
    StandardModuli.Abelian.ComplexAbelianPresentation A where
  variety := P.variety
  comparison := e ≪≫ P.comparison
  comparison_group := by
    change IsMonHom (e.hom ≫ P.comparison.hom)
    infer_instance

def AlgebraicEnhancement.Abelian.CMEnhancement.onPresentedFiber
    {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A) (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety) :
    AbelianEndomorphism.AbelianEndomorphismTuple (Fin E.size) A where
  map i := P.comparison.hom ≫ E.map i ≫ P.comparison.inv
  group i := by infer_instance

theorem PresentedTupleComparison.Abelian.conjugate_through_iso_recovery
    {C : Type*} [Category* C] {X Y Z : C} (e : X ≅ Y) (d : Y ≅ Z)
    (m : Z ⟶ Z) (n : X ⟶ X)
    (h : CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms e n (d.hom ≫ m ≫ d.inv)) :
    (e ≪≫ d).inv ≫ n ≫ (e ≪≫ d).hom = m := by
  dsimp only [CoefficientEndomorphismComparison.Abelian.ConjugateEndomorphisms] at h
  rw [h]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc,
    e.inv_hom_id_assoc, d.inv_hom_id_assoc, d.inv_hom_id, Category.comp_id]

theorem PresentedTupleComparison.Abelian.presented_tuple_recovery
    {g : ℕ} {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (P : StandardModuli.Abelian.ComplexAbelianPresentation B) (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety)
    (a : AbelianEndomorphism.AbelianEndomorphismTuple (Fin E.size) A)
    (h : AbelianEndomorphism.ConjugateAbelianTuples e a (E.onPresentedFiber P)) :
    ∀ i, (P.transport e).comparison.inv ≫ a.map i ≫ (P.transport e).comparison.hom = E.map i :=
  fun i => PresentedTupleComparison.Abelian.conjugate_through_iso_recovery e P.comparison (E.map i) (a.map i) (h i)

end

end OAI.ArithmeticGeometry.Descent.CMVariety
