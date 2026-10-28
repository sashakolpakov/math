import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness

/-! # Source Morphism Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceMorphismSpecialization.Coefficients

noncomputable section

/-! Fixed-source specialization commutes with every actual morphism
between two original arithmetic schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem fixedSourceModel_specialization_map (s : Finset K)
    (X Y : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (a : X ⟶ Y) :
    (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization ≫
        ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).map a).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map a).left ≫
        (CoefficientModels.Coefficients.fixedSourceModel R K s Y hY).specialization := by
  let F := Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let H := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let eX := (CoefficientModels.Coefficients.fixedSourceComparison R K s).app X
  let eY := (CoefficientModels.Coefficients.fixedSourceComparison R K s).app Y
  let qX := pullback.fst (F.obj X).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let qY := pullback.fst (F.obj Y).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  have hn : (H.map a).left ≫ eY.inv.left = eX.inv.left ≫ (G.map (F.map a)).left :=
    congrArg Over.Hom.left ((CoefficientModels.Coefficients.fixedSourceComparison R K s).inv.naturality a)
  have hq : (G.map (F.map a)).left ≫ qY = qX ≫ (F.map a).left := pullback.lift_fst _ _ _
  change (eX.inv.left ≫ qX) ≫ (F.map a).left = (H.map a).left ≫ (eY.inv.left ≫ qY)
  rw [Category.assoc, ← hq, ← Category.assoc, ← hn, Category.assoc]

theorem fixedSourceModel_noetherian [IsNoetherianRing R] (s : Finset K)
    (X : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    IsNoetherian (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).model.left := by
  let M := CoefficientModels.Coefficients.fixedSourceModel R K s X hX
  have : IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K M.coefficients) :=
    Coefficient.Finiteness.Coefficients.coefficientBase_locallyNoetherian R K M.coefficients
  have hfp := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation (CoefficientModels.Coefficients.parameterBaseMap R K s) X hX
  have : LocallyOfFinitePresentation M.model.hom := hfp.1
  have : QuasiCompact M.model.hom := hfp.2.1
  have : IsLocallyNoetherian M.model.left := LocallyOfFiniteType.isLocallyNoetherian M.model.hom
  have : CompactSpace M.model.left := QuasiCompact.compactSpace_of_compactSpace M.model.hom
  exact ⟨⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceMorphismSpecialization.Coefficients
