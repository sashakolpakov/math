import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement

/-! # Source Specialization Naturality -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceSpecializationNaturality.Coefficients

noncomputable section

/-! Specialization to a fixed-source coefficient model commutes with
the actual base changes of every original endomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem fixedSourceModel_specialization_naturality (s : Finset K) (X : Over (Spec (.of R)))
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (a : X ⟶ X) :
    (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization ≫
        ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).map a).left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map a).left ≫
        (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization := by
  let F := Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)
  let G := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  let H := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let e := (CoefficientModels.Coefficients.fixedSourceComparison R K s).app X
  let q := pullback.fst (F.obj X).hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)
  have hn : (H.map a).left ≫ e.inv.left = e.inv.left ≫ (G.map (F.map a)).left :=
    congrArg Over.Hom.left ((CoefficientModels.Coefficients.fixedSourceComparison R K s).inv.naturality a)
  have hq : (G.map (F.map a)).left ≫ q = q ≫ (F.map a).left := pullback.lift_fst _ _ _
  change (e.inv.left ≫ q) ≫ (F.map a).left = (H.map a).left ≫ (e.inv.left ≫ q)
  rw [Category.assoc, ← hq, ← Category.assoc, ← hn, Category.assoc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceSpecializationNaturality.Coefficients
