import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.FineTarget
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PolarizationCancellation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateTransport

/-! # Intrinsic Fine Target Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction

noncomputable section

section

/-! The actual Noetherian fine-moduli target retains the full integral
Tate preimage, and its polarization map is uniquely determined. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left] (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (n : ℕ) (hn : 0 < n) {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * d) T.left}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B) [Etale f.hom.left]
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B) (level : B.FullLevel N)
  (hσ : ∀ a, A.action.map a ≫ f.hom = f.hom ≫ σ.map a)
  (hker : ∀ (U : Over T.left) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
  (hlag : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ T.left),
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.polarized.abelian.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.polarized.abelian.pullback s) (A.polarized.dual.pullback s)
      (A.polarized.polarization.pullback s) n hn).relativeAnnihilator H = H)
  (hc : Nat.Coprime n ((∏ j, P.polarizationType j) ^ 2))

variable (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)

set_option backward.isDefEq.respectTransparency false in
theorem noetherianQuotientTargetIsogeny_tate_preimage
    (U : Over T.left) (q : ℕ) [Fact q.Prime] :
    let e := Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM
    letI : IsMonHom e.hom := e.preservesGroup
    TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) e.hom =
      TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) f.hom :=
  TateTransport.Construction.finePELClassifyingIsogeny_tate_preimage M hM
    (Noetherian.PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc) f U q

set_option backward.isDefEq.respectTransparency false in
theorem noetherianQuotientTargetIsogeny_polarization_unique
    (ε : Fin (3 * d) → ℕ)
    (r : AbelianModuli.HilbertConstruction.PolarizationData.Polarization
      (M.universal.polarized.dual.pullback
        (Noetherian.FineTarget.Construction.noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM).left) ε)
    (hr :
      let e := Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM
      e.hom ≫ r.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom
        A.polarized.dual (M.universal.polarized.dual.pullback
          (Noetherian.FineTarget.Construction.noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM).left) =
          A.polarized.polarization.isogeny.hom ^ n) :
    r.isogeny = (M.universal.polarized.polarization.pullback
      (Noetherian.FineTarget.Construction.noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM).left).isogeny := by
  apply PolarizationAssembly.Construction.isogeny_eq_of_hom_eq
  apply Noetherian.PolarizationCancellation.Construction.noetherian_polarizationPullback_injective
    (Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM)
    A.polarized.dual _
  exact hr.trans (Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny_polarization A n hn f σ level hσ hker hlag hc M hM).symm

end

/-! An actual fine-moduli target carries the quotient isogeny and its
full polarization, integral action, and ordered marking comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))}

structure NativeFinePELTarget (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) (n : ℕ)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) where
  target : T ⟶ M.space
  isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian
    (M.universal.polarized.abelian.pullback target.left)
  etale : Etale isogeny.hom.left
  polarization : isogeny.hom ≫ (M.universal.polarized.polarization.pullback target.left).isogeny.hom ≫
    FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap isogeny.hom A.polarized.dual
      (M.universal.polarized.dual.pullback target.left) = A.polarized.polarization.isogeny.hom ^ n
  action : ∀ a, isogeny.hom ≫ (Over.pullback target.left).map (M.universal.action.map a) =
    A.action.map a ≫ isogeny.hom
  marking : ∀ (U : Over T.left)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))),
    (A.polarized.level.hom.app (.op U) c).val ≫ isogeny.hom =
      ((M.universal.polarized.level.pullback target.left).hom.app (.op U) c).val
  polarization_unique : ∀ (ε : Fin (3 * d) → ℕ)
    (r : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (M.universal.polarized.dual.pullback target.left) ε),
    isogeny.hom ≫ r.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap isogeny.hom
      A.polarized.dual (M.universal.polarized.dual.pullback target.left) =
      A.polarized.polarization.isogeny.hom ^ n →
    r.isogeny = (M.universal.polarized.polarization.pullback target.left).isogeny

variable [CharZero K] [IsLocallyNoetherian T.left] (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (n : ℕ) (hn : 0 < n) {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * d) T.left}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B) [Etale f.hom.left]
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B) (level : B.FullLevel N)
  (hσ : ∀ a, A.action.map a ≫ f.hom = f.hom ≫ σ.map a)
  (hker : ∀ (U : Over T.left) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom), x ^ n = 1)
  (hlag : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ T.left),
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.polarized.abelian.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.polarized.abelian.pullback s) (A.polarized.dual.pullback s)
      (A.polarized.polarization.pullback s) n hn).relativeAnnihilator H = H)
  (hc : Nat.Coprime n ((∏ j, P.polarizationType j) ^ 2))
  (hlevel : ∀ (U : Over T.left)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))),
    (level.hom.app (.op U) c).val = (A.polarized.level.hom.app (.op U) c).val ≫ f.hom)
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)

def noetherianQuotientFineTargetData : NativeFinePELTarget A n M where
  target := Noetherian.FineTarget.Construction.noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM
  isogeny := Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM
  etale := Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny_etale A n hn f σ level hσ hker hlag hc M hM
  polarization := Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny_polarization A n hn f σ level hσ hker hlag hc M hM
  action := Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny_action A n hn f σ level hσ hker hlag hc M hM
  marking := Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny_marking A n hn f σ level hσ hker hlag hc M hM hlevel
  polarization_unique := noetherianQuotientTargetIsogeny_polarization_unique A n hn f σ level hσ hker hlag hc M hM

theorem noetherianQuotientFineTargetData_kernel :
    Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (noetherianQuotientFineTargetData A n hn f σ level hσ hker hlag hc hlevel M hM).isogeny.hom =
      Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom :=
  Noetherian.FineTarget.Construction.noetherianQuotientTargetIsogeny_kernel A n hn f σ level hσ hker hlag hc M hM

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction
