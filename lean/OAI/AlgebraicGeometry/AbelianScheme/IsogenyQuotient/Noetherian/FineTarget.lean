import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELPolarization

/-! # Fine Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.FineTarget.Construction

noncomputable section

/-! The actual Noetherian quotient has a fine-moduli target retaining
its kernel, action, full ordered marking, and positive polarization identity. -/

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

def noetherianQuotientTarget : T ⟶ M.space :=
  FinePELTarget.Construction.finePELClassifyingMap M hM (PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc)

def noetherianQuotientTargetIsogeny :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian
      (M.universal.polarized.abelian.pullback
        (noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM).left) :=
  FinePELTarget.Construction.finePELClassifyingIsogeny M hM (PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc) f

theorem noetherianQuotientTargetIsogeny_kernel :
    Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM).hom =
      Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom :=
  FinePELTarget.Construction.finePELClassifyingIsogeny_kernel M hM (PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc) f

set_option backward.isDefEq.respectTransparency false in
theorem noetherianQuotientTargetIsogeny_etale :
    Etale (noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM).hom.left :=
  FinePELTarget.Construction.finePELClassifyingIsogeny_etale M hM (PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc) f

set_option backward.isDefEq.respectTransparency false in
theorem noetherianQuotientTargetIsogeny_polarization :
    let target := noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM
    let e := noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM
    e.hom ≫ (M.universal.polarized.polarization.pullback target.left).isogeny.hom ≫
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom A.polarized.dual
        (M.universal.polarized.dual.pullback target.left) =
          A.polarized.polarization.isogeny.hom ^ n :=
  (FinePELPolarization.Construction.finePELClassifyingIsogeny_polarization_pullback M hM
    (PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc)
    A.polarized.dual f).trans
      (PEL.Construction.noetherianQuotientPEL_polarization A n hn f σ level hσ hker hlag hc)

theorem noetherianQuotientTargetIsogeny_action (a : NumberField.RingOfIntegers E) :
    let target := noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM
    let e := noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM
    e.hom ≫ (Over.pullback target.left).map (M.universal.action.map a) =
      A.action.map a ≫ e.hom :=
  FinePELTarget.Construction.finePELClassifyingIsogeny_action M hM
    (PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc) f
    A.action (fun a => (hσ a).symm) a

theorem noetherianQuotientTargetIsogeny_marking
    (hlevel : ∀ (U : Over T.left)
      (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))),
      (level.hom.app (.op U) c).val =
        (A.polarized.level.hom.app (.op U) c).val ≫ f.hom)
    (U : Over T.left)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))) :
    let target := noetherianQuotientTarget A n hn f σ level hσ hker hlag hc M hM
    let e := noetherianQuotientTargetIsogeny A n hn f σ level hσ hker hlag hc M hM
    (A.polarized.level.hom.app (.op U) c).val ≫ e.hom =
      ((M.universal.polarized.level.pullback target.left).hom.app (.op U) c).val :=
  FinePELTarget.Construction.finePELClassifyingIsogeny_marking M hM
    (PEL.Construction.noetherianQuotientPEL A n hn f σ level hσ hker hlag hc) f
    A.polarized.level (fun U c => (hlevel U c).symm) U c

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.FineTarget.Construction
