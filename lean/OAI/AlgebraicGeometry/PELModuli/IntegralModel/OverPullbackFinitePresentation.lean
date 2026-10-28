import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness

/-! # Over Pullback Finite Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverPullbackFinitePresentation

noncomputable section

/-! Finite presentation of the actual fiber-product model, used when
extending a cartesian generic-family comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem over_pullback_finitePresentation {S : Scheme.{0}} {X Y Z : Over S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (hg : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism g.left) :
    ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback f g).hom := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  let p := pullback.fst f g
  have hs := ((IsPullback.of_hasPullback f g).map (Over.forget S)).flip
  have : LocallyOfFinitePresentation p.left := MorphismProperty.of_isPullback hs hg.1
  have : QuasiCompact p.left := MorphismProperty.of_isPullback hs hg.2.1
  have : QuasiSeparated p.left := MorphismProperty.of_isPullback hs hg.2.2
  rw [← p.w]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem coefficient_pullback_finitePresentation
    {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K] {s : Finset K}
    {X Y Z : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (hZ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Z.hom) :
    ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback f g).hom := by
  have : IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s) := Coefficient.Finiteness.Coefficients.coefficientBase_locallyNoetherian R K s
  exact over_pullback_finitePresentation f g hX (Coefficient.Finiteness.Coefficients.morphism_of_models_finitePresentation Y Z hY hZ g)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverPullbackFinitePresentation
