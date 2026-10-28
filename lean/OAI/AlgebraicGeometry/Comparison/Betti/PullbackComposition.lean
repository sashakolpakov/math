import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ConstantSquare

/-! # Pullback Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PullbackComposition

noncomputable section

/-! Canonical composition comparisons for actual Zariski inverse image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z)

def inverseImageCompIso : Algebraic.Sheaves.inverseImage g ⋙ Algebraic.Sheaves.inverseImage f ≅ Algebraic.Sheaves.inverseImage (f ≫ g) :=
  ((Algebraic.Sheaves.imageAdjunction g).comp (Algebraic.Sheaves.imageAdjunction f)).leftAdjointUniq (Algebraic.Sheaves.imageAdjunction (f ≫ g))

def inverseImageComplexCompIso :
    (Algebraic.Sheaves.inverseImage g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (Algebraic.Sheaves.inverseImage (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  ((OpenForms.imageComplexAdjunctionInt g).comp (OpenForms.imageComplexAdjunctionInt f)).leftAdjointUniq
    (OpenForms.imageComplexAdjunctionInt (f ≫ g))

theorem inverseImageCompIso_onComplexes (K : CochainComplex (Algebraic.Sheaves.ComplexSheaves Z) ℤ) :
    (NatTrans.mapHomologicalComplex (inverseImageCompIso f g).hom (ComplexShape.up ℤ)).app K =
      (inverseImageComplexCompIso f g).hom.app K := by
  have h := AdjunctionComplexUniqueness.onComplexes_leftAdjointUniq (ComplexShape.up ℤ)
    ((Algebraic.Sheaves.imageAdjunction g).comp (Algebraic.Sheaves.imageAdjunction f)) (Algebraic.Sheaves.imageAdjunction (f ≫ g)) K
  erw [AdjunctionComplexUniqueness.onComplexes_comp (ComplexShape.up ℤ) (Algebraic.Sheaves.imageAdjunction g) (Algebraic.Sheaves.imageAdjunction f)] at h
  exact h.symm

theorem inverseImageCompIso_constant :
    (Algebraic.Sheaves.inverseImage f).map (Algebraic.Sheaves.inverseImageConstantIso g).hom ≫ (Algebraic.Sheaves.inverseImageConstantIso f).hom =
      (inverseImageCompIso f g).hom.app (Algebraic.Sheaves.constantComplexSheaf Z) ≫
        (Algebraic.Sheaves.inverseImageConstantIso (f ≫ g)).hom := by
  let a := Analytification.ConstantSquare.zariskiConstantAdjunction Z
  let b := Algebraic.Sheaves.imageAdjunction g
  let c := Algebraic.Sheaves.imageAdjunction f
  let d := Analytification.ConstantSquare.zariskiConstantAdjunction Y
  let e := Analytification.ConstantSquare.zariskiConstantAdjunction X
  let q := Algebraic.Sheaves.imageAdjunction (f ≫ g)
  let m := ModuleCat.of ℂ ℂ
  have hw := AdjunctionComposition.leftAdjointUniq_whiskerRight (a.comp b) d c m
  have h₁ := (Adjunction.leftAdjointUniq_trans_app ((a.comp b).comp c) (d.comp c) e m).symm.trans
    (congrArg (fun t => t ≫ ((d.comp c).leftAdjointUniq e).hom.app m) hw)
  erw [AdjunctionComposition.comp_assoc a b c] at h₁
  have hl := AdjunctionComposition.leftAdjointUniq_whiskerLeft a (b.comp c) q m
  have h₂ := Adjunction.leftAdjointUniq_trans_app (a.comp (b.comp c)) (a.comp q) e m
  erw [hl] at h₂
  exact h₁.symm.trans h₂.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.PullbackComposition
