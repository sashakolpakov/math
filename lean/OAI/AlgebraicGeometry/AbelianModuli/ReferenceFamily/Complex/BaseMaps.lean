import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexUniversal

/-! # Base Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Complex test maps retain their original underlying morphisms
when the coefficient field is restricted. The native complex-family
classifying map is natural and detects the map to the complex fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] (κ : K →+* ℂ)

def Complex.BaseMaps.complexBaseRestrictionMap {S T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ T) :
    Complex.BallPeriods.restrictComplexBase κ S ⟶ Complex.BallPeriods.restrictComplexBase κ T :=
  Over.homMk f.left (by
    change f.left ≫ (T.hom ≫ Spec.map (CommRingCat.ofHom κ)) =
      S.hom ≫ Spec.map (CommRingCat.ofHom κ)
    rw [← Category.assoc, f.w])

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N)

theorem Models.FinePELModel.complexFamilyBaseMap_comp {S T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (g : T ⟶ S) :
    M.complexFamilyBaseMap κ (g ≫ f) = Complex.BaseMaps.complexBaseRestrictionMap κ g ≫ M.complexFamilyBaseMap κ f := by
  apply Over.OverMorphism.ext
  exact Category.assoc g.left f.left (pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ)))

theorem Models.FinePELModel.complexFamilyBaseMap_injective (S : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Function.Injective (M.complexFamilyBaseMap κ (S := S)) := by
  intro f g h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg Over.Hom.left h
  · exact f.w.trans g.w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
