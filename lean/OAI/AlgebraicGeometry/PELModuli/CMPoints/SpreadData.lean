import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentDiagram
import OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadActions
import OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadScalarFactorization
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveTransport

/-! # Spread Data -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The constructed CM diagram over an arithmetic base, with full
relative actions and the actual scalar splitting recovered from its arrows. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveTransport

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

structure Models.RankThreePELModel.CMSpreadData (hM : M.HasPrescribedBallPeriods) (a : M.Family)
    (t : Fin (M.componentCount a)) where
  component : M.CMComponentFactorData hM a t
  arithmetic : ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel (component.diagram M) (component.diagramModels M)
  spread : AbelianDiagramSpreading.SpreadFiniteAbelianDiagram arithmetic.diagram arithmetic.embedding
  denominator_divides : M.arithmetic.denominator ∣ spread.base.denominator

section

variable {M} {hM : M.HasPrescribedBallPeriods} {a : M.Family} {t : Fin (M.componentCount a)}
  (C : M.CMSpreadData hM a t)

abbrev Models.RankThreePELModel.CMSpreadData.base := C.spread.base

def Models.RankThreePELModel.CMSpreadData.original : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * M.s) C.base.base := C.spread.abelian (0 : Fin 4)

def Models.RankThreePELModel.CMSpreadData.factor (i : Fin 3) : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (Fintype.card (NumberField.InfinitePlace E)) C.base.base :=
  C.spread.abelian i.succ

def Models.RankThreePELModel.CMSpreadData.action (i : Fin 3) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (C.factor i) :=
  SpreadActions.ScalarFactorDiagram.spreadFullAction _ _ C.component.splitting
    (Module.finBasis ℤ (NumberField.RingOfIntegers E)) (fun i => (C.component.factor i).integralAction)
    (C.component.originalModel M) C.component.factorModel C.arithmetic C.spread i

def Models.RankThreePELModel.CMSpreadData.splitting : TorsionFactorIso.AbelianScalarFactorization C.original C.factor :=
  SpreadScalarFactorization.ScalarFactorDiagram.spreadRelativeSplitting _ _ C.component.splitting
    (Module.finBasis ℤ (NumberField.RingOfIntegers E)) (fun i => (C.component.factor i).integralAction)
    (C.component.originalModel M) C.component.factorModel C.arithmetic C.spread

def Models.RankThreePELModel.CMSpreadData.pointFieldEmbedding : C.component.field →+* C.base.extension.carrier :=
  C.arithmetic.spreadModelField C.spread (0 : Fin 4)

theorem Models.RankThreePELModel.CMSpreadData.pointFieldEmbedding_compatible :
    C.base.embedding.comp C.pointFieldEmbedding = C.component.field.subtype :=
  C.arithmetic.spreadModelField_compatible C.spread (0 : Fin 4)

def Models.RankThreePELModel.CMSpreadData.originalFieldEmbedding : M.arithmetic.extension.carrier →+* C.base.extension.carrier :=
  C.pointFieldEmbedding.comp C.component.fieldEmbedding

theorem Models.RankThreePELModel.CMSpreadData.originalFieldEmbedding_compatible :
    C.base.embedding.comp C.originalFieldEmbedding = M.arithmetic.embedding := by
  rw [Models.RankThreePELModel.CMSpreadData.originalFieldEmbedding, ← RingHom.comp_assoc, Models.RankThreePELModel.CMSpreadData.pointFieldEmbedding_compatible]
  exact C.component.field_compatible

def Models.RankThreePELModel.CMSpreadData.coefficientEmbedding : E →+* C.base.extension.carrier :=
  C.originalFieldEmbedding.comp M.extendedEmbedding

def Models.RankThreePELModel.CMSpreadData.factorComplexIso (i : Fin 3) :
    ((C.factor i).pullback C.base.complexPoint).scheme ≅ (C.component.factor i).abelianScheme.scheme :=
  C.arithmetic.spreadComplexComparison C.spread i.succ

def Models.RankThreePELModel.CMSpreadData.factorProjective (i : Fin 3) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation ((C.factor i).pullback C.base.complexPoint).scheme.left
      ((C.factor i).pullback C.base.complexPoint).scheme.hom := by
  let e := C.factorComplexIso i
  let P := (C.component.factor i).realization.abelianVariety.variety.presentation.projective
  have H := P.transportIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e)
  change Foundations.Scheme.SmoothProjective.ProjectivePresentation _ (e.hom.left ≫ (C.component.factor i).abelianScheme.scheme.hom) at H
  rw [e.hom.w] at H
  exact H

end

theorem Models.RankThreePELModel.exists_CM_spread_data
    [IsGalois ℚ E]
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hCMAbelianVarietyA : Descent.AbelianInput) (hCMAbelianVarietyM : Descent.ModuliInput)
    (hM : M.HasPrescribedBallPeriods) (a : M.Family) (t : Fin (M.componentCount a)) :
    Nonempty (M.CMSpreadData hM a t) := by
  obtain ⟨C, Q, R, hR⟩ := M.exists_spread_CM_component_diagram hHilb hEnd hCMAbelianVarietyA hCMAbelianVarietyM hM a t
  exact ⟨⟨C, Q, R, hR⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
