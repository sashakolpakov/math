import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.ChosenPEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.PELClassifyingTarget

/-! # Complex Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexTarget.Construction

noncomputable section

/-! Each raw split coset constructs its own geometric PEL quotient
and actual fine-moduli target, independently of a universal parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

def identityTotalParameterPoint {S : Scheme.{0}} (T : Over S) :
    T ⟶ TotalParameters.Construction.totalParameter T (Over.mk (𝟙 T.left)) :=
  Over.homMk (𝟙 T.left) (by simp only [TotalParameters.Construction.totalParameter, Over.mk_left, Over.mk_hom, Category.id_comp])

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
  {d N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk c))
  {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
  (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
  (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
  (h : ℕ) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
  (M : Fin d → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module (ZMod (q ^ h)) (M v)] [∀ v, Finite (M v)]
  (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
  (eM : ∀ v, M v ≃+ (∀ i, ZMod (q ^ a v i)))

local instance rawComplexSource_noetherian : IsLocallyNoetherian (Over.mk c).left :=
  inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)

local instance rawComplexParameter_noetherian : IsLocallyNoetherian (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)).left :=
  inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)

def originalComplexRawKernel
    (x : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant))) :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) :=
  let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let b := Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual A.polarized.polarization
    (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels b
  ChoiceKernel.Construction.choiceFullKernel (q ^ h) d M p r ep
    ((ComplexChoices.Construction.originalComplexRawChoices A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM).symm x)

variable (hcop : Nat.Coprime q N) (hpol : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i) (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0})

include hcop hpol hlabels h_FiniteDescent in
theorem originalComplexRawKernel_quotient
    (x : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant))) :
    Noetherian.RelativePEL.Construction.RelativePELQuotient A (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
      (originalComplexRawKernel A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM x) (q ^ h) :=
  Noetherian.ChosenPEL.Construction.noetherian_chosen_pel_quotient A q hcop h hpol j arithmeticEmbedding hsplit labels hlabels M
    (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) h_FiniteDescent
    ((ComplexChoices.Construction.originalComplexRawChoices A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM).symm x)

variable (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)

def originalComplexRawTarget
    (x : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant))) :
    Over.mk c ⟶ Z.space :=
  identityTotalParameterPoint (Over.mk c) ≫
    (originalComplexRawKernel_quotient A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
      hcop hpol hlabels h_FiniteDescent x).target Z hZ

theorem originalComplexRawTarget_classifies
    (x : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant))) :
    let H := originalComplexRawKernel_quotient A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
      hcop hpol hlabels h_FiniteDescent x
    FinePELTarget.Construction.finePELClassifyingMap Z hZ (H.object.pullback (identityTotalParameterPoint (Over.mk c))) =
      originalComplexRawTarget A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
        hcop hpol hlabels h_FiniteDescent Z hZ x := by
  exact FinePELPolarization.Construction.finePELClassifyingMap_pullback Z hZ _ (identityTotalParameterPoint (Over.mk c))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexTarget.Construction
