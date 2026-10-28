import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComposition
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness

/-! # Image Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ImageComposition

noncomputable section

/-! Canonical composition comparisons for the native inverse-image functors and coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R]

def constantAdjunction (X : Over (Spec (CommRingCat.of R))) :
    constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat R) ⊣
      (sheafSections (Opens.grothendieckTopology X.left) (ModuleCat R)).obj (op ⊤) :=
  constantSheafAdj (Opens.grothendieckTopology X.left) (ModuleCat R) isTerminalTop

variable {X Y Z : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (g : Y ⟶ Z)

def inverseImageCompIso : Int.inverseImage g ⋙ Int.inverseImage f ≅ Int.inverseImage (f ≫ g) :=
  ((Int.imageAdjunction g).comp (Int.imageAdjunction f)).leftAdjointUniq (Int.imageAdjunction (f ≫ g))

def inverseImageComplexCompIso :
    (Int.inverseImage g).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        (Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      (Int.inverseImage (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℕ) :=
  ((Int.imageComplexAdjunction g).comp (Int.imageComplexAdjunction f)).leftAdjointUniq
    (Int.imageComplexAdjunction (f ≫ g))

theorem inverseImageCompIso_onComplexes (K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Z) ℕ) :
    (NatTrans.mapHomologicalComplex (inverseImageCompIso f g).hom (ComplexShape.up ℕ)).app K =
      (inverseImageComplexCompIso f g).hom.app K := by
  have h := AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.onComplexes_leftAdjointUniq (ComplexShape.up ℕ)
    ((Int.imageAdjunction g).comp (Int.imageAdjunction f)) (Int.imageAdjunction (f ≫ g)) K
  erw [AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.onComplexes_comp (ComplexShape.up ℕ) (Int.imageAdjunction g) (Int.imageAdjunction f)] at h
  exact h.symm

theorem inverseImageCompIso_constant :
    (Int.inverseImage f).map (Int.inverseImageConstantIso g).hom ≫ (Int.inverseImageConstantIso f).hom =
      (inverseImageCompIso f g).hom.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Z) ≫
        (Int.inverseImageConstantIso (f ≫ g)).hom := by
  let a := constantAdjunction Z
  let b := Int.imageAdjunction g
  let c := Int.imageAdjunction f
  let d := constantAdjunction Y
  let e := constantAdjunction X
  let q := Int.imageAdjunction (f ≫ g)
  let m := ModuleCat.of R R
  have hw := AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.leftAdjointUniq_whiskerRight (a.comp b) d c m
  have h₁ := (Adjunction.leftAdjointUniq_trans_app ((a.comp b).comp c) (d.comp c) e m).symm.trans
    (congrArg (fun t => t ≫ ((d.comp c).leftAdjointUniq e).hom.app m) hw)
  erw [AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.comp_assoc a b c] at h₁
  have hl := AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.leftAdjointUniq_whiskerLeft a (b.comp c) q m
  have h₂ := Adjunction.leftAdjointUniq_trans_app (a.comp (b.comp c)) (a.comp q) e m
  erw [hl] at h₂
  exact h₁.symm.trans h₂.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ImageComposition
