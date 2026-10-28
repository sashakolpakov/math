import OAI.AlgebraicGeometry.PELModuli.CMPoints.ProjectiveEndomorphismDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedModelProjectivity
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EndomorphismParameterDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticTowerCoherence

/-! # Endomorphism Number Field Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EndomorphismNumberFieldDescent

noncomputable section

/-! Finite-extension descent of every specified finite endomorphism tuple.
Projectivity is constructed after a finite extension and the resulting
tower is collapsed with the original arithmetic abelian model retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem intertwining_after_conjugation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {Z : D} (e : X ≅ Y) (d : F.obj X ≅ Z) (c : F.obj Y ≅ Z)
    (r : X ⟶ X) (s : Z ⟶ Z)
    (hc : F.map e.hom ≫ c.hom = d.hom)
    (hr : F.map r ≫ d.hom = d.hom ≫ s) :
    F.map (e.inv ≫ r ≫ e.hom) ≫ c.hom = c.hom ≫ s := by
  have hcancel : F.map e.inv ≫ d.hom = c.hom := by
    rw [← hc, ← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.id_comp]
  rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc, hc, hr,
    ← Category.assoc, hcancel]

theorem endomorphism_tuple_descends
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {g n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (r : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ)))) :
    ∃ (F : IntegralModel.Base.ArithmeticBaseExtension K κ)
      (rF : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback F.fieldExtension)),
      ∀ i, (Over.pullback (Spec.map (CommRingCat.ofHom F.embedding))).map ((rF i).hom _) ≫
          (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F A.scheme).hom =
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F A.scheme).hom ≫ (r i).hom _ := by
  classical
  obtain ⟨B, ⟨BA⟩⟩ := FixedModelProjectivity.fixed_abelian_model_projective_after_finite_extension κ A
  let AB := A.pullback B.fieldExtension
  let eB : (AB.pullback (Spec.map (CommRingCat.ofHom B.embedding))).scheme ≅
      (A.pullback (Spec.map (CommRingCat.ofHom κ))).scheme := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B A.scheme
  let : IsMonHom eB.hom := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_isMonHom B A.scheme
  let : IsMonHom eB.symm.hom := inferInstanceAs (IsMonHom eB.inv)
  let rB (i : Fin n) : IntegralModel.Finite.Actions.GroupEndRing (AB.pullback (Spec.map (CommRingCat.ofHom B.embedding))) :=
    IntegralModel.Finite.Actions.GroupEndRing.transport eB.symm (r i)
  obtain ⟨C, rC, _, hC⟩ := ProjectiveEndomorphismDescent.projective_endomorphism_tuple_descends_native
    hHilb hEnd B.embedding AB BA rB
  let F := B.compose C
  let AF : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of C.extension.carrier)) := A.pullback F.fieldExtension
  let e : (AB.pullback C.fieldExtension).scheme ≅ AF.scheme :=
    (B.composeSourceNatIso C).app A.scheme
  have he : IsMonHom e.hom :=
    IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom A.scheme B.fieldExtension C.fieldExtension F.fieldExtension
      (B.compose_fieldExtension C)
  let := he
  let rF (i : Fin n) : IntegralModel.Finite.Actions.GroupEndRing AF :=
    IntegralModel.Finite.Actions.GroupEndRing.transport e (rC i)
  let Ψ := Over.pullback (Spec.map (CommRingCat.ofHom C.embedding))
  let cB : Ψ.obj (AB.pullback C.fieldExtension).scheme ≅
      (AB.pullback (Spec.map (CommRingCat.ofHom B.embedding))).scheme :=
    IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso C AB.scheme
  let d : Ψ.obj (AB.pullback C.fieldExtension).scheme ≅
      (A.pullback (Spec.map (CommRingCat.ofHom κ))).scheme :=
    IntegralModel.Arithmetic.TowerComparison.arithmeticTowerComplexSourceIso B C A.scheme
  let c : Ψ.obj AF.scheme ≅ (A.pullback (Spec.map (CommRingCat.ofHom κ))).scheme :=
    IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F A.scheme
  have hd : Ψ.map e.hom ≫ c.hom = d.hom := ArithmeticTowerCoherence.arithmetic_tower_complex_comparison B C A.scheme
  refine ⟨F, rF, fun i => ?_⟩
  have h₁ : Ψ.map ((rC i).hom _) ≫ cB.hom = cB.hom ≫ (rB i).hom _ :=
    EndomorphismParameterDescent.arithmetic_endomorphism_restrict_compatibility AB C (rC i) (rB i) (hC i)
  have h₂ : (rB i).hom _ ≫ eB.hom = eB.hom ≫ (r i).hom _ := by
    change (eB.hom ≫ (r i).hom _ ≫ eB.inv) ≫ eB.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₃ : Ψ.map ((rC i).hom _) ≫ d.hom = d.hom ≫ (r i).hom _ := by
    change Ψ.map ((rC i).hom _) ≫ cB.hom ≫ eB.hom = _
    rw [← Category.assoc, h₁, Category.assoc, h₂]
    exact (Category.assoc _ _ _).symm
  exact intertwining_after_conjugation Ψ e d c ((rC i).hom _) ((r i).hom _) hd h₃

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EndomorphismNumberFieldDescent
