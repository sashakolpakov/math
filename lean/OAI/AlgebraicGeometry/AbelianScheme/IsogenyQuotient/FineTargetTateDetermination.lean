import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELTateAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FineTargetUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelDetermination

/-! # Fine Target Tate Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! The full actual integral Tate preimage determines the entire fine
moduli target on geometric fibers. Equality of full kernels is derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

variable {E K k : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [Field k] [CharZero k] [IsAlgClosed k]
  {d N q h : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {s : Spec (.of k) ⟶ Spec (.of K)}
  {A B C : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (Over.mk s)}

local instance FineTargetTateDetermination.Construction.fineTargetGeometricBase_noetherian : IsLocallyNoetherian (Over.mk s).left :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

theorem Intrinsic.PELBaseChange.Construction.NativePELQuotient.sameKernel_of_tate_preimage_eq
    (f : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B (q ^ h)) (r : Intrinsic.PELBaseChange.Construction.NativePELQuotient A C (q ^ h))
    (hq : Nat.Coprime q (∏ i, P.polarizationType i))
    (he : TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) r.isogeny.hom) :
    Isogenies.NeighborCounting.QuotientComparison.SameKernel f.isogeny r.isogeny :=
  TateComparison.PELIsogenies.PELIsogeny.kernel_eq_all_tests_of_preimage_eq f.tateIsogeny r.tateIsogeny P.polarizationType
    A.polarized.polarization.kernelType B.polarized.polarization.kernelType C.polarized.polarization.kernelType hq he

theorem IntrinsicFineTargetData.Construction.NativeFinePELTarget.target_eq_of_tate_preimage_eq
    {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N} (hM : M.IsFine)
    (f r : IntrinsicFineTargetData.Construction.NativeFinePELTarget A (q ^ h) M)
    (hq : Nat.Coprime q (∏ i, P.polarizationType i))
    (he : TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) r.isogeny.hom) :
    f.target = r.target :=
  f.target_eq_of_sameKernel hM r (f.toQuotient.sameKernel_of_tate_preimage_eq r.toQuotient hq he)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
