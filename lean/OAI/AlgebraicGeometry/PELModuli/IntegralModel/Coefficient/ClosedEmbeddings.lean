import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FractionField
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedImmersionDescent

/-! # Closed Embeddings -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.ClosedEmbeddings.Coefficients

noncomputable section

/-! A closed embedding after extension to the ambient field is already
a closed embedding over the fraction field of its coefficient model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {s : Finset K}

theorem closedImmersion_fraction_model
    {X Y : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)} (f : X ⟶ Y)
    [IsClosedImmersion ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).map f).left] :
    IsClosedImmersion ((Over.pullback (FractionField.Coefficients.fractionBaseMap R K s)).map f).left := by
  let g := FractionField.Coefficients.fractionBaseMap R K s
  let ψ := FractionField.Coefficients.ambientFieldMap R K s
  let F := Over.pullback g
  let G := Over.pullback ψ
  let H := Over.pullback (ψ ≫ g)
  have : IsClosedImmersion (H.map f).left := by
    change IsClosedImmersion ((Over.pullback (FractionField.Coefficients.ambientFieldMap R K s ≫ FractionField.Coefficients.fractionBaseMap R K s)).map f).left
    rw [FractionField.Coefficients.fractionBase_factorization]
    infer_instance
  let eX := (Over.pullbackComp ψ g).app X
  let eY := (Over.pullbackComp ψ g).app Y
  have : IsIso eX.hom.left := ((Over.forget (Spec (.of K))).mapIso eX).isIso_hom
  have : IsIso eY.hom.left := ((Over.forget (Spec (.of K))).mapIso eY).isIso_hom
  have hn : (H.map f).left ≫ eY.hom.left = eX.hom.left ≫ (G.map (F.map f)).left :=
    congrArg Over.Hom.left ((Over.pullbackComp ψ g).hom.naturality f)
  have hc : IsClosedImmersion ((H.map f).left ≫ eY.hom.left) := inferInstance
  rw [hn] at hc
  have : IsClosedImmersion (G.map (F.map f)).left :=
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion eX.hom.left _).mp hc
  exact ClosedImmersionDescent.closedImmersion_of_fpqc_baseChange ψ (F.map f)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.ClosedEmbeddings.Coefficients
