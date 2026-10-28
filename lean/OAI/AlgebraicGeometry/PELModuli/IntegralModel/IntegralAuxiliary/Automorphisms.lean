import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Classification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Relabel

/-! # Automorphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! Classify each relabeled universal integral PEL family to construct
actual parameter maps and universal-family comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

def IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelMap (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) : X ⟶ X :=
  U.classifyingMap hU X (U.relabelAuxiliary (LocallyConstant.const _ σ))

def IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelComparison (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback (U.auxiliaryRelabelMap hU σ))
      (U.relabelAuxiliary (LocallyConstant.const _ σ)) :=
  U.classifyingIso hU X (U.relabelAuxiliary (LocallyConstant.const _ σ))

def IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelPullbackComparison {T : Over (Spec (.of R))} (f : T ⟶ X)
    (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback (f ≫ U.auxiliaryRelabelMap hU σ))
      ((U.pullback f).relabelAuxiliary (LocallyConstant.const _ σ)) :=
  (U.pullbackCompIso (U.auxiliaryRelabelMap hU σ) f).symm.trans
    (((U.auxiliaryRelabelComparison hU σ).pullback f).trans
      (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.ofEq (U.relabelAuxiliary_pullback (LocallyConstant.const _ σ) f)))

def IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelCompositionComparison (σ τ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) :
    IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback (U.auxiliaryRelabelMap hU σ ≫ U.auxiliaryRelabelMap hU τ))
      (U.relabelAuxiliary (LocallyConstant.const _ (σ * τ))) :=
  (U.auxiliaryRelabelPullbackComparison hU (U.auxiliaryRelabelMap hU σ) τ).trans
    (((U.auxiliaryRelabelComparison hU σ).relabelAuxiliary (LocallyConstant.const _ τ)).trans
      (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.ofEq (U.relabelAuxiliary_mul (LocallyConstant.const _ σ) (LocallyConstant.const _ τ))))

end

/-! The constructed integral auxiliary-label maps satisfy the group
law as actual scheme morphisms and are actual automorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelMap_one : U.auxiliaryRelabelMap hU 1 = 𝟙 X := by
  symm
  exact U.classifying_unique hU X _ (𝟙 X)
    (U.pullbackIdIso.trans (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.ofEq U.relabelAuxiliary_one.symm))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelMap_mul (σ τ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) :
    U.auxiliaryRelabelMap hU σ ≫ U.auxiliaryRelabelMap hU τ =
      U.auxiliaryRelabelMap hU (σ * τ) :=
  U.classifying_unique hU X _ _ (U.auxiliaryRelabelCompositionComparison hU σ τ)

def IntegralAdded.PELId.IntegralAddedPELLevel.auxiliaryRelabelIso (σ : AbelianModuli.HilbertConstruction.Level.Parameters.LevelLabelAut (3 * s) L) : X ≅ X where
  hom := U.auxiliaryRelabelMap hU σ
  inv := U.auxiliaryRelabelMap hU σ⁻¹
  hom_inv_id := by rw [U.auxiliaryRelabelMap_mul, mul_inv_cancel, U.auxiliaryRelabelMap_one]
  inv_hom_id := by rw [U.auxiliaryRelabelMap_mul, inv_mul_cancel, U.auxiliaryRelabelMap_one]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
