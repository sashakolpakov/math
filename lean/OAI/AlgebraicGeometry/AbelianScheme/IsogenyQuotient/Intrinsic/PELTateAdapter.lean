import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies

/-! # PEL Tate Adapter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic

noncomputable section

/-! The actual positive PEL quotient supplies TateComparison's native Tate
isogeny data, with its original dual map and Poincare class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))}

def PELTateAdapter.Construction.nativePELTateFamily (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) :
    TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * d) N T.left :=
  TateComparison.PEL.PELFamilyData.ofPolarized A.polarized (TateComparison.PELAdapters.actionToEnd A.action)

def PELBaseChange.Construction.NativePELQuotient.tateIsogeny [IsLocallyNoetherian T.left]
    {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T} (f : PELBaseChange.Construction.NativePELQuotient A B n) :
    TateComparison.PELIsogenies.PELIsogeny (PELTateAdapter.Construction.nativePELTateFamily A) (PELTateAdapter.Construction.nativePELTateFamily B) n where
  isogeny := f.isogeny
  dualHom := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.isogeny.hom A.polarized.dual B.polarized.dual
  dualGroup := Noetherian.DualMaps.Construction.noetherian_nativeDualMap_isMonHom f.isogeny.hom A.polarized.dual B.polarized.dual
  poincare := (Noetherian.DualPoincare.Construction.noetherian_nativeDualMap_poincare A.polarized.dual B.polarized.dual f.isogeny.hom).symm
  equivariant a := by
    change TateComparison.End.endSchemeMap A.polarized.abelian.scheme (TateComparison.PELAdapters.actionToEnd A.action a) ≫ f.isogeny.hom =
      f.isogeny.hom ≫ TateComparison.End.endSchemeMap B.polarized.abelian.scheme (TateComparison.PELAdapters.actionToEnd B.action a)
    rw [TateComparison.PELAdapters.actionToEnd_schemeMap, TateComparison.PELAdapters.actionToEnd_schemeMap]
    exact (f.action a).symm
  polarization := f.polarization
  marking := f.marking

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic
