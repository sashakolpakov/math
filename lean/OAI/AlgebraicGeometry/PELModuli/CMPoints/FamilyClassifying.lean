import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexClassifying
import OAI.ArithmeticGeometry.Descent.CMVariety.PulledBackPresentations
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PolarizedIntrinsicPresentation

/-! # Family Classifying -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FamilyClassifying

noncomputable section

/-! Classifying points and actual fiber presentations for a pulled-back
PEL family, with the original coefficient embedding and scheme retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (κ : K →+* ℂ) {S : Over Foundations.Scheme.ProjectiveSpace.complexBase}

def PELFamilyClassifyingPoint
    (f : Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom κ)) ⟶ M.space)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) : Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ M.space :=
  Over.homMk (x.left ≫ f.left) (by
    rw [Category.assoc, f.w]
    change x.left ≫ (S.hom ≫ Spec.map (CommRingCat.ofHom κ)) = Spec.map (CommRingCat.ofHom κ)
    rw [← Category.assoc, x.w]
    exact Category.id_comp _)

def PELFamilyPresentation
    (f : Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom κ)) ⟶ M.space)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation ((M.universal.polarized.abelian.pullback f.left).pullback x.left) :=
  ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation.pullbackComp M.universal.polarized.abelian f.left x.left
    (PolarizedIntrinsicPresentation.polarizedNativePresentation (M.universal.polarized.pullback (x.left ≫ f.left)))

def PELComplexFamilyMap (f : S ⟶ M.complexFiber κ) :
    Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom κ)) ⟶ M.space :=
  Over.homMk (f.left ≫ CategoryTheory.Limits.pullback.fst M.space.hom
    (Spec.map (CommRingCat.ofHom κ))) (by
      change (f.left ≫ CategoryTheory.Limits.pullback.fst M.space.hom
        (Spec.map (CommRingCat.ofHom κ))) ≫ M.space.hom = S.hom ≫ Spec.map (CommRingCat.ofHom κ)
      dsimp [AbelianModuli.ReferenceFamily.Models.FinePELModel.complexFiber, Over.pullback] at f ⊢
      rw [Category.assoc, CategoryTheory.Limits.pullback.condition, ← Category.assoc]
      exact congrArg (fun a => a ≫ Spec.map (CommRingCat.ofHom κ)) f.w)

omit [NumberField K] in
theorem PELFamilyClassifyingPoint_complexMap (f : S ⟶ M.complexFiber κ) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    PELFamilyClassifyingPoint M κ (PELComplexFamilyMap M κ f) x =
      ComplexClassifying.finePELClassifyingPoint M κ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) := by
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm

omit [NumberField K] in
theorem PELFamilyClassifyingPoint_injective (f : S ⟶ M.complexFiber κ) [IsOpenImmersion f.left] :
    Function.Injective (PELFamilyClassifyingPoint M κ (PELComplexFamilyMap M κ f)) := by
  intro x y hxy
  rw [PELFamilyClassifyingPoint_complexMap, PELFamilyClassifyingPoint_complexMap] at hxy
  have h := ComplexClassifying.finePELClassifyingPoint_injective M κ hxy
  apply Over.OverMorphism.ext
  exact (cancel_mono f.left).mp (congrArg Over.Hom.left h)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FamilyClassifying
