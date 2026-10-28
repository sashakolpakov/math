import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TargetRealization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FineTargetTateDetermination

/-! # Target Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

section

/-! Full scheme-kernel equality identifies an actual geometric fine
target with the independently constructed raw PEL quotient target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

set_option backward.isDefEq.respectTransparency false in
theorem IntrinsicFineTargetData.Construction.NativeFinePELTarget.target_eq_of_quotient_sameKernel
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T} {Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N} (hZ : Z.IsFine)
    (f : IntrinsicFineTargetData.Construction.NativeFinePELTarget A n Z) (r : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n)
    (hk : Isogenies.NeighborCounting.QuotientComparison.SameKernel f.isogeny r.isogeny) : f.target = FinePELTarget.Construction.finePELClassifyingMap Z hZ B := by
  let e := Noetherian.Comparison.Construction.noetherianQuotientPELIso A (Z.universal.pullback f.target) B f.isogeny r.isogeny hk
    (f.polarization.trans r.polarization.symm) f.action r.action f.marking r.marking
  have hc := FinePELPolarization.Construction.finePELClassifyingMap_eq_of_iso Z hZ e
  have ht := FinePELTarget.Construction.finePELClassifyingMap_unique Z hZ (Z.universal.pullback f.target) f.target
    ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.canonical Z.universal f.target⟩
  exact ht.trans hc

set_option backward.isDefEq.respectTransparency false in
theorem IntrinsicFineTargetData.Construction.NativeFinePELTarget.target_eq_of_quotient_tate_preimage_eq
    {E K k : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [Field k] [CharZero k] [IsAlgClosed k]
    {d N q h : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    {c : Spec (.of k) ⟶ Spec (.of K)} {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk c)}
    {Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N} (hZ : Z.IsFine)
    (f : IntrinsicFineTargetData.Construction.NativeFinePELTarget A (q ^ h) Z) (r : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B (q ^ h))
    (hq : Nat.Coprime q (∏ i, P.polarizationType i))
    (he : TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) r.isogeny.hom) :
    f.target = FinePELTarget.Construction.finePELClassifyingMap Z hZ B := by
  let : IsLocallyNoetherian (Over.mk c).left := inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  exact f.target_eq_of_quotient_sameKernel hZ r (f.toQuotient.sameKernel_of_tate_preimage_eq r hq he)

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
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)

local instance TargetDetermination.Construction.rawKernelTargetDetermination_noetherian : IsLocallyNoetherian (Over.mk c).left :=
  inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)

set_option backward.isDefEq.respectTransparency false in
theorem TargetDetermination.Construction.originalComplexRawTarget_eq_of_kernel
    (x : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)))
    (f : IntrinsicFineTargetData.Construction.NativeFinePELTarget A (q ^ h) Z)
    (hf : ∀ (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) (z : U ⟶ A.polarized.abelian.scheme),
      z ≫ f.isogeny.hom = 1 ↔ z ∈
        (Reference.ComplexTarget.Construction.originalComplexRawKernel A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM x).points U
          (Over.homMk U.hom (Category.comp_id U.hom))) :
    f.target = Reference.ComplexTarget.Construction.originalComplexRawTarget A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
      hcop hpol hlabels h_FiniteDescent Z hZ x := by
  obtain ⟨B, r, ht, hr⟩ := TargetRealization.Construction.originalComplexRawTarget_realized A j arithmeticEmbedding hsplit hd hdegree
    h labels M a ha hdominant eM hcop hpol hlabels h_FiniteDescent Z hZ x
  have hk : Isogenies.NeighborCounting.QuotientComparison.SameKernel f.isogeny r.isogeny := fun U z => (hf U z).trans (hr U z).symm
  exact (f.target_eq_of_quotient_sameKernel hZ r hk).trans ht

end

/-! The classifying point of any actual quotient with the full raw
kernel equals the independently constructed raw target point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

theorem Intrinsic.PELBaseChange.Construction.NativePELQuotient.classifying_eq_of_sameKernel
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    {A B C : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T} (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
    (f : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n) (r : Intrinsic.PELBaseChange.Construction.NativePELQuotient A C n)
    (hk : Isogenies.NeighborCounting.QuotientComparison.SameKernel f.isogeny r.isogeny) :
    FinePELTarget.Construction.finePELClassifyingMap Z hZ B = FinePELTarget.Construction.finePELClassifyingMap Z hZ C :=
  FinePELPolarization.Construction.finePELClassifyingMap_eq_of_iso Z hZ
    (Noetherian.Comparison.Construction.noetherianQuotientPELIso A B C f.isogeny r.isogeny hk
      (f.polarization.trans r.polarization.symm) f.action r.action f.marking r.marking)

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
  (hcop : Nat.Coprime q N) (hpol : Nat.Coprime (q ^ h) ((∏ i, P.polarizationType i) ^ 2))
  (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
  (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)

local instance TargetDetermination.Construction.rawQuotientTarget_noetherian : IsLocallyNoetherian (Over.mk c).left :=
  inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)

theorem TargetDetermination.Construction.originalComplexRawQuotient_target_eq_of_kernel
    (x : Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel d q) (TateComparison.HeckeKernel.representative d q (SplitHeckeChoices.Construction.naturalIntegralLocalType d h a hdominant)))
    {B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk c)} (f : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B (q ^ h))
    (hf : ∀ (U : Over Foundations.Scheme.ProjectiveSpace.complexBase) (z : U ⟶ A.polarized.abelian.scheme),
      z ≫ f.isogeny.hom = 1 ↔ z ∈
        (Reference.ComplexTarget.Construction.originalComplexRawKernel A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM x).points U
          (Over.homMk U.hom (Category.comp_id U.hom))) :
    FinePELTarget.Construction.finePELClassifyingMap Z hZ B =
      Reference.ComplexTarget.Construction.originalComplexRawTarget A j arithmeticEmbedding hsplit hd hdegree h labels M a ha hdominant eM
        hcop hpol hlabels h_FiniteDescent Z hZ x := by
  obtain ⟨C, r, ht, hr⟩ := TargetRealization.Construction.originalComplexRawTarget_realized A j arithmeticEmbedding hsplit hd hdegree
    h labels M a ha hdominant eM hcop hpol hlabels h_FiniteDescent Z hZ x
  have hk : Isogenies.NeighborCounting.QuotientComparison.SameKernel f.isogeny r.isogeny := fun U z => (hf U z).trans (hr U z).symm
  exact (f.classifying_eq_of_sameKernel Z hZ r hk).trans ht

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
