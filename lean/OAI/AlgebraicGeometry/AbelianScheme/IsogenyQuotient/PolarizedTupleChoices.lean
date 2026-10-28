import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Choices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeChoices

/-! # Polarized Tuple Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedTupleChoices.Construction

noncomputable section

/-!
The actual geometric points of the subgroup parameter are the raw split
Hecke support, with a single multiplier. The equivalence is assembled
from the original geometric subgroups and their constructed Tate bases.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
  {N : ℕ} (F : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N Foundations.Scheme.ProjectiveSpace.complexBase)
  {δ : Fin (3 * s) → ℕ} {c : NumberField.RingOfIntegers E →+* NumberField.RingOfIntegers E}
  (hF : F.IsPEL δ c) (n : ℕ) (label : Fin s → Gal(E/ℚ))
  (M : Fin s → Type) [∀ v, AddCommGroup (M v)]
  [∀ v, Module (ZMod (q ^ n)) (M v)] [∀ v, Finite (M v)]
  (a : Fin s → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ n) (hdominant : ∀ v, Antitone (a v))
  (eM : ∀ v, M v ≃+ (∀ i, ZMod (q ^ a v i)))

def polarizedTupleChoiceFunctor : (Over Foundations.Scheme.ProjectiveSpace.complexBase)ᵒᵖ ⥤ Type 1 :=
  Parameter.Products.Construction.blockTupleFunctor s (fun v => SubgroupFunctor.Construction.supportedSubgroupFunctor F.abelian.scheme (q ^ n) (M v)
    ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n (label v))))

def polarizedTupleRawChoices :
    (polarizedTupleChoiceFunctor j iota hsplit s F n label M).obj (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) ≃
      Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q)
        (TateComparison.HeckeKernel.representative s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant)) :=
  ((Universal.Choices.Construction.blockTupleCoordinates s (fun v => SubgroupFunctor.Construction.supportedSubgroupFunctor F.abelian.scheme (q ^ n) (M v)
      ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n (label v))))
        (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).trans
    (Equiv.piCongrRight fun v => PolarizedChoices.Construction.polarizedSupportedRawChoices j iota hsplit s hs hdegree F hF
      n (label v) (M v) (a v) (ha v) (hdominant v) (eM v))).trans
    (SplitHeckeChoices.Construction.splitRawBlockSupportEquiv s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant)).symm

theorem polarizedTupleRawChoices_block
    (H : (polarizedTupleChoiceFunctor j iota hsplit s F n label M).obj
      (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) (v : Fin s) :
    SplitHeckeChoices.Construction.splitRawBlockSupportEquiv s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant)
      (polarizedTupleRawChoices j iota hsplit s hs hdegree F hF n label M a ha hdominant eM H) v =
    PolarizedChoices.Construction.polarizedSupportedRawChoices j iota hsplit s hs hdegree F hF n (label v) (M v)
      (a v) (ha v) (hdominant v) (eM v)
      (Universal.Choices.Construction.blockTupleCoordinates s (fun w => SubgroupFunctor.Construction.supportedSubgroupFunctor F.abelian.scheme (q ^ n) (M w)
        ((TateComparison.PELAdapters.actionFromEnd F.action).map (j.projector iota hsplit n (label w))))
          (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) H v) := by
  change ((SplitHeckeChoices.Construction.splitRawBlockSupportEquiv s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant))
    ((SplitHeckeChoices.Construction.splitRawBlockSupportEquiv s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant)).symm _)) v = _
  exact congrFun
    ((SplitHeckeChoices.Construction.splitRawBlockSupportEquiv s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant)).apply_symm_apply _) v

def polarizedParameterRawChoices {P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (repr : (polarizedTupleChoiceFunctor j iota hsplit s F n label M).RepresentableBy P) :
    (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ P) ≃
      Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q)
        (TateComparison.HeckeKernel.representative s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant)) :=
  repr.homEquiv.trans
    (polarizedTupleRawChoices j iota hsplit s hs hdegree F hF n label M a ha hdominant eM)

theorem polarizedParameterRawChoices_coefficient {P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (repr : (polarizedTupleChoiceFunctor j iota hsplit s F n label M).RepresentableBy P)
    (x : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ P) :
    TateComparison.HeckeKernel.kernel (TateComparison.HeckeKernel.integralLevel s q)
      (SplitHeckeTopology.Construction.rawIntegralTypeOperator s q (SplitHeckeChoices.Construction.naturalIntegralLocalType s n a hdominant))
      (polarizedParameterRawChoices j iota hsplit s hs hdegree F hF
        n label M a ha hdominant eM repr x).val = 1 := by
  let y := polarizedParameterRawChoices j iota hsplit s hs hdegree F hF
    n label M a ha hdominant eM repr x
  change TateComparison.HeckeKernel.kernel (TateComparison.HeckeKernel.integralLevel s q) (HeckeKernel.Construction.sphericalHeckeFromKernel _ _ _) y.val = 1
  rw [HeckeKernel.Construction.sphericalHeckeFromKernel_kernel, Hecke.Construction.rawDoubleCosetKernel_apply, ite_eq_left y.property]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizedTupleChoices.Construction
