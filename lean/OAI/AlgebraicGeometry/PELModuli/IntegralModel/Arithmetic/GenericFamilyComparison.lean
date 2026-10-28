import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FineComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AddedGenericFamily
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FieldExtensionReduced

/-! # Generic Family Comparison -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel

/-! The actual generic universal family of the constructed integral
fine model is compared with ReferenceFamily's given universal family after reduction
and the specified number-field extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (iota : E →+* K)
    {Q : Over B.base}

def PEL.Has.IntegralPELObject.genericIntegralFamily
    (U : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Q) :
    PEL.Has.IntegralPELObject P B.extension.carrier
      ((algebraMap K B.extension.carrier).comp
        (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) N
      ((Over.pullback B.generic).obj Q) :=
  (U.baseChange B.toField).changeEmbedding (Arithmetic.AddedGenericFamily.arithmetic_generic_reference_embedding B iota)

theorem Arithmetic.GenericFamilyComparison.arithmetic_pel_generic_comparison [IsReduced Q.left]
    (U : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Q)
    (hU : ∀ (T : Over B.base) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N T),
      ∃! f : T ⟶ Q, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data))
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) :
    ∃ e : (Over.pullback B.generic).obj Q ≅ Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M,
      Nonempty (PEL.Iso.PolarizedActionIso ((Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback e.hom).data
        (U.genericIntegralFamily B iota).data) := by
  have : IsReduced ((Over.pullback B.generic).obj Q).left := B.genericFiber_isReduced Q
  have : IsReduced (Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M).left := B.fieldExtension_isReduced (Reduction.reduction M.space)
  exact IntegralPEL.FineComparison.integralPEL_fine_comparison ((Over.pullback B.generic).obj Q) (Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M)
    (U.genericIntegralFamily B iota) (Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M)
    (IntegralPEL.FineComparison.integralPEL_fine_changeEmbedding (U.baseChange B.toField)
      (Arithmetic.AddedGenericFamily.arithmetic_generic_reference_embedding B iota) (IntegralPEL.FineBaseChange.integralPEL_fine_baseChange U hU B.toField))
    (Reduced.Generic.reduced_generic_finePEL_action_classifies (algebraMap K B.extension.carrier) M hM)

end AlgebraicGeometry.PELModuli.IntegralModel

namespace AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericFamilyComparison

/-! Construct the exact IntegralPELSpread record with ReferenceFamily's supplied
universal family. The generic family comparison retains its abelian and
dual schemes, polarization, Poincare class, full level, and integral action. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame.ArithmeticPELComparison
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    {Q : Over B.base} (U : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N Q)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

def referenceComparisonToFamilyIso
    (e : (Over.pullback B.generic).obj Q ≅ ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M)
    (a : PEL.Iso.PolarizedActionIso ((ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback e.hom).data
      (U.genericIntegralFamily B iota).data) :
    PEL.Has.PulledBackPELDataIso U.data (PEL.Has.characteristicZeroPELData P M.universal)
      (pullback.fst Q.hom B.generic)
      (e.hom.left ≫ pullback.fst (Reduction.reduction M.space).hom B.fieldExtension ≫ (Reduction.reductionι M.space).left) := by
  let V := PEL.Has.characteristicZeroPELData P M.universal
  let r := (Reduction.reductionι M.space).left
  let q := pullback.fst (Reduction.reduction M.space).hom B.fieldExtension
  let c : PEL.Iso.PolarizedActionIso (U.data.pullback (pullback.fst Q.hom B.generic))
      (V.pullback (e.hom.left ≫ q ≫ r)) :=
    a.symm.trans ((PEL.Iso.PolarizedActionIso.pullbackComp (V.pullback r) q e.hom.left).trans
      ((PEL.Iso.PolarizedActionIso.pullbackComp V r (e.hom.left ≫ q)).trans
        (PEL.Iso.PolarizedActionIso.pullbackCongr V _ _ (Category.assoc e.hom.left q r))))
  exact PEL.Has.PulledBackPELDataIso.ofActionIso c

def integralPELSpreadOfFineModel [IsReduced Q.left]
    (hU : ∀ (T : Over B.base) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N T),
      ∃! f : T ⟶ Q, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data)) (hM : M.IsFine) :
    PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B := by
  let e := (arithmetic_pel_generic_comparison B iota U hU M hM).choose
  let a := Classical.choice (arithmetic_pel_generic_comparison B iota U hU M hM).choose_spec
  exact {
    toOver := Q
    universal := U
    genericIso := e
    familyIso := referenceComparisonToFamilyIso B U M e a }

theorem spread_moduli_of_action_classification
    (V : PEL.Has.IntegralPELSpread P iota κ N M.space M.universal B)
    (hV : ∀ (T : Over B.base) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N T),
      ∃! f : T ⟶ V.toOver, Nonempty (PEL.Iso.PolarizedActionIso (V.universal.pullback f).data A.data)) :
    V.IsReducedPELModuli P := by
  intro T _ A
  obtain ⟨f, ⟨e⟩, hu⟩ := hV T A
  refine ⟨f, ⟨PEL.Has.PulledBackPELDataIso.ofActionIso (e.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data).symm)⟩, ?_⟩
  rintro g ⟨a⟩
  exact hu g ⟨a.toActionIso.trans (PEL.Iso.PolarizedActionIso.pullbackId A.data)⟩

theorem integralPELSpreadOfFineModel_isReducedPELModuli [IsReduced Q.left]
    (hU : ∀ (T : Over B.base) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N T),
      ∃! f : T ⟶ Q, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data)) (hM : M.IsFine) :
    (integralPELSpreadOfFineModel B U M hU hM).IsReducedPELModuli P :=
  spread_moduli_of_action_classification B M (integralPELSpreadOfFineModel B U M hU hM) hU

end AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericFamilyComparison

end

end OAI
