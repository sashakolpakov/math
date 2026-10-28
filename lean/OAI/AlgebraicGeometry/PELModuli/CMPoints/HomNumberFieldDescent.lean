import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianProducts
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EndomorphismNumberFieldDescent

/-! # Hom Number Field Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HomNumberFieldDescent

noncomputable section

/-! All arrows of a finite complex diagram descend over one finite
extension, with the given arithmetic models and canonical complex
comparisons unchanged. Each arrow is a matrix entry of a descended
endomorphism of one constructed abelian product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem finite_abelian_homomorphisms_descend
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {r m : ℕ} (d : Fin r → ℕ) (A : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) (Spec (.of K)))
    (source target : Fin m → Fin r)
    (f : ∀ j, ((A (source j)).pullback (Spec.map (CommRingCat.ofHom κ))).scheme ⟶
      ((A (target j)).pullback (Spec.map (CommRingCat.ofHom κ))).scheme)
    (hf : ∀ j, IsMonHom (f j)) :
    ∃ F : IntegralModel.Base.ArithmeticBaseExtension K κ,
      ∃ fF : ∀ j, ((A (source j)).pullback F.fieldExtension).scheme ⟶
        ((A (target j)).pullback F.fieldExtension).scheme,
        (∀ j, IsMonHom (fF j)) ∧
        ∀ j, (Over.pullback (Spec.map (CommRingCat.ofHom F.embedding))).map (fF j) ≫
            (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F (A (target j)).scheme).hom =
          (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F (A (source j)).scheme).hom ≫ f j := by
  obtain ⟨C⟩ := AbelianProducts.exists_abelian_retract_container r d A
  let (i : Fin r) : IsMonHom (C.inclusion i) := C.inclusion_group i
  let (i : Fin r) : IsMonHom (C.projection i) := C.projection_group i
  let (j : Fin m) : IsMonHom (f j) := hf j
  let H := Over.pullback (Spec.map (CommRingCat.ofHom κ))
  let fH (j : Fin m) : H.obj (A (source j)).scheme ⟶ H.obj (A (target j)).scheme := f j
  let (j : Fin m) : IsMonHom (fH j) := hf j
  let uHom (j : Fin m) : H.obj C.abelian.scheme ⟶ H.obj C.abelian.scheme :=
    H.map (C.projection (source j)) ≫ fH j ≫ H.map (C.inclusion (target j))
  have uHom_group (j : Fin m) : IsMonHom (uHom j) := by
    dsimp only [uHom]
    infer_instance
  let u (j : Fin m) := @IntegralModel.Finite.Actions.GroupEndRing.ofHom _ _
    (C.abelian.pullback (Spec.map (CommRingCat.ofHom κ))) (uHom j) (uHom_group j)
  obtain ⟨F, uF, huF⟩ := EndomorphismNumberFieldDescent.endomorphism_tuple_descends hHilb hEnd κ C.abelian u
  let Q := Over.pullback F.fieldExtension
  let G := Over.pullback (Spec.map (CommRingCat.ofHom F.embedding))
  let uFHom (j : Fin m) : Q.obj C.abelian.scheme ⟶ Q.obj C.abelian.scheme := (uF j).hom _
  let (j : Fin m) : IsMonHom (uFHom j) := inferInstanceAs (IsMonHom ((uF j).hom _))
  have huF' (j : Fin m) : G.map (uFHom j) ≫ (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F C.abelian.scheme).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F C.abelian.scheme).hom ≫ uHom j := huF j
  let fF (j : Fin m) : Q.obj (A (source j)).scheme ⟶ Q.obj (A (target j)).scheme :=
    Q.map (C.inclusion (source j)) ≫ uFHom j ≫ Q.map (C.projection (target j))
  refine ⟨F, fF, fun j => ?_, fun j => ?_⟩
  · exact inferInstanceAs (IsMonHom (Q.map (C.inclusion (source j)) ≫ uFHom j ≫
      Q.map (C.projection (target j))))
  · have hi : G.map (Q.map (C.inclusion (source j))) ≫
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F C.abelian.scheme).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F (A (source j)).scheme).hom ≫ H.map (C.inclusion (source j)) :=
      (IntegralModel.Arithmetic.ComplexComparison.GroupBaseChange.arithmeticComplexNatIso F).hom.naturality (C.inclusion (source j))
    have hp : G.map (Q.map (C.projection (target j))) ≫
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F (A (target j)).scheme).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F C.abelian.scheme).hom ≫ H.map (C.projection (target j)) :=
      (IntegralModel.Arithmetic.ComplexComparison.GroupBaseChange.arithmeticComplexNatIso F).hom.naturality (C.projection (target j))
    have hs : H.map (C.inclusion (source j)) ≫ H.map (C.projection (source j)) =
        𝟙 (H.obj (A (source j)).scheme) := by
      rw [← H.map_comp, C.retraction, H.map_id]
    have ht : H.map (C.inclusion (target j)) ≫ H.map (C.projection (target j)) =
        𝟙 (H.obj (A (target j)).scheme) := by
      rw [← H.map_comp, C.retraction, H.map_id]
    have hrec : H.map (C.inclusion (source j)) ≫ uHom j ≫
        H.map (C.projection (target j)) = fH j :=
      AbelianProducts.recover_arrow_from_retracts _ _ _ _ hs ht (fH j)
    change G.map (Q.map (C.inclusion (source j)) ≫ uFHom j ≫
      Q.map (C.projection (target j))) ≫ (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F (A (target j)).scheme).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F (A (source j)).scheme).hom ≫ fH j
    rw [G.map_comp, G.map_comp, Category.assoc, Category.assoc, hp,
      ← Category.assoc (G.map (uFHom j)), huF' j,
      Category.assoc, ← Category.assoc (G.map (Q.map (C.inclusion (source j)))), hi,
      Category.assoc, hrec]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HomNumberFieldDescent
