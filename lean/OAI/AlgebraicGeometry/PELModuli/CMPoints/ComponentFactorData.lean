import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralCoordinate
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiberFactorization

/-! # Component Factor Data -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! Constructed arithmetic CM-point data on every supplied component,
including three actual integral CM factors and their scalar splitting. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

structure Models.RankThreePELModel.CMComponentFactorData (hM : M.HasPrescribedBallPeriods)
    (a : M.Family) (t : Fin (M.componentCount a)) where
  field : Subfield ℂ
  [numberField : NumberField field]
  fieldEmbedding : M.arithmetic.extension.carrier →+* field
  field_compatible : field.subtype.comp fieldEmbedding = M.arithmetic.embedding
  point : Spec (.of field) ⟶ ((M.components a).S t).left
  point_base : point ≫ ((M.components a).S t).hom =
    Spec.map (CommRingCat.ofHom fieldEmbedding) ≫ M.arithmetic.generic
  factor : ∀ i : Fin 3, IntegralModel.CMIntegralModel (PeriodCoordinates.coordinateCMType (M.datum a) (hM.2.2 a).1 i)
  factorModel : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (factor i).abelianScheme
  splitting : TorsionFactorIso.AbelianScalarFactorization
    ((M.componentPolarized a t).abelian.pullback (Spec.map (CommRingCat.ofHom field.subtype) ≫ point))
    (fun i => (factor i).abelianScheme)

attribute [instance] Models.RankThreePELModel.CMComponentFactorData.numberField

def Models.RankThreePELModel.CMComponentFactorData.originalModel
    {hM : M.HasPrescribedBallPeriods} {a : M.Family} {t : Fin (M.componentCount a)}
    (C : M.CMComponentFactorData hM a t) :
    AbelianArithmeticModels.AbelianNumberFieldModel
      ((M.componentPolarized a t).abelian.pullback
        (Spec.map (CommRingCat.ofHom C.field.subtype) ≫ C.point)) :=
  IntrinsicFiberFactorization.abelianNumberFieldModelOfFiber (M.componentPolarized a t).abelian C.field C.point

theorem Models.RankThreePELModel.exists_CM_component_factor_data
    [IsGalois ℚ E]
    (hCMAbelianVarietyA : Descent.AbelianInput) (hCMAbelianVarietyM : Descent.ModuliInput)
    (hM : M.HasPrescribedBallPeriods) (a : M.Family) (t : Fin (M.componentCount a)) :
    Nonempty (M.CMComponentFactorData hM a t) := by
  obtain ⟨F, hF, i, p, hi, hp, hCM⟩ :=
    M.exists_coordinate_CM_native_arithmetic_component_point hCMAbelianVarietyM hM a t
  let : NumberField F := hF
  obtain ⟨C, hC, ⟨D⟩⟩ := IntrinsicFiberFactorization.exists_coordinate_CM_fiber_factorization hCMAbelianVarietyA
    (M.componentPolarized a t) (Spec.map (CommRingCat.ofHom F.subtype) ≫ p) hCM
  exact ⟨⟨F, i, hi, p, hp, C,
    fun j => Classical.choice ((C j).hasAbelianNumberFieldModel (hC j)), D⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
