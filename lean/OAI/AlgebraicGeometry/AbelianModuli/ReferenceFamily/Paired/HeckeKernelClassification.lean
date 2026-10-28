import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NoetherianPairedHeckeSource
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.KernelParameterChoice

/-! # Hecke Kernel Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Every typed paired PEL quotient of the universal family's actual
pullback has a unique map to the constructed finite etale kernel
parameter, on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    {A : PEL.Objects.PELObject P iota N T} {hn : 0 < n}
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]

omit [NumberField K] [CharZero K] in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.classifiesKernel (R : NoetherianPairedHeckeSource.PairedHeckeSource A n hn M)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (X : Over T.left) (B : PEL.Objects.PELObject P iota N (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T X))
    (f : Paired.PELQuotients.PairedPELQuotient (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T X)) B n)
    (hM : (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom).HasModuleType M) :
    ∃! k : X ⟶ R.parameter,
      R.subgroup.baseChange k = Paired.KernelParameterChoice.pairedKernelParameterChoice A X B f M hM := by
  apply (R.classify X (Paired.KernelParameterChoice.pairedKernelParameterChoice A X B f M hM)).mp
  exact ⟨Paired.KernelParameterChoice.pairedKernelParameterChoice_stable A X B f M hM,
    Paired.KernelParameterChoice.pairedKernelParameterChoice_self_annihilating A X B f M hM hn hdegree⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
