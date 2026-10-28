import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.FineTarget

/-! # Quotient Fine Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.QuotientFineTarget.Construction

noncomputable section

/-! The constructed isotropic PEL quotient yields the actual fine target
with its full kernel, integral action, ordered marking, and polarization uniqueness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
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

variable (hlevel : ∀ (U : Over T.left)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))),
    (level.hom.app (.op U) c).val = (A.polarized.level.hom.app (.op U) c).val ≫ f.hom)

set_option backward.isDefEq.respectTransparency false in
def universalFunctionQuotientNativeData :
    Intrinsic.PELBaseChange.Construction.NativePELQuotient A (PEL.Construction.universalFunctionQuotientPEL A hA n hn f σ level hσ hker hlag hc) n where
  isogeny := f
  etale := inferInstance
  polarization := PEL.Construction.universalFunctionQuotientPEL_polarization A hA n hn f σ level hσ hker hlag hc
  action a := (hσ a).symm
  marking U c := (hlevel U c).symm

variable (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)

def universalFunctionQuotientFineTargetData : IntrinsicFineTargetData.Construction.NativeFinePELTarget A n M :=
  (universalFunctionQuotientNativeData A hA n hn f σ level hσ hker hlag hc hlevel).universalFunctionFineTarget hA M hM

theorem universalFunctionQuotientFineTargetData_kernel :
    Intrinsic.MorphismKernel.Construction.nativeMorphismKernel
      (universalFunctionQuotientFineTargetData A hA n hn f σ level hσ hker hlag hc hlevel M hM).isogeny.hom =
      Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom :=
  (universalFunctionQuotientNativeData A hA n hn f σ level hσ hker hlag hc hlevel).universalFunctionFineTarget_kernel hA M hM

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.QuotientFineTarget.Construction
