import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.Comparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELPolarization

/-! # Fine Target Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! The full kernel determines the actual fine target. The comparison
derives polarization, Poincare, action, and marking compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
  {A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T} {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N}

theorem IntrinsicFineTargetData.Construction.NativeFinePELTarget.target_eq_of_sameKernel (hM : M.IsFine)
    (f r : IntrinsicFineTargetData.Construction.NativeFinePELTarget A n M) (hk : Isogenies.NeighborCounting.QuotientComparison.SameKernel f.isogeny r.isogeny) : f.target = r.target := by
  apply FinePELPolarization.Construction.finePELMaps_eq_of_pullback_iso M hM f.target r.target
  exact Noetherian.Comparison.Construction.noetherianQuotientPELIso A (M.universal.pullback f.target) (M.universal.pullback r.target)
    f.isogeny r.isogeny hk (f.polarization.trans r.polarization.symm)
    f.action r.action f.marking r.marking

theorem IntrinsicFineTargetData.Construction.NativeFinePELTarget.target_eq_of_kernel (hM : M.IsFine)
    (f r : IntrinsicFineTargetData.Construction.NativeFinePELTarget A n M)
    (hk : Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.isogeny.hom = Intrinsic.MorphismKernel.Construction.nativeMorphismKernel r.isogeny.hom) :
    f.target = r.target := by
  apply f.target_eq_of_sameKernel hM r
  intro U a
  let t : U ⟶ Over.mk (𝟙 T.left) := Over.homMk U.hom (Category.comp_id _)
  exact iff_of_eq (congrArg (fun H => a ∈ H.points U t) hk)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
