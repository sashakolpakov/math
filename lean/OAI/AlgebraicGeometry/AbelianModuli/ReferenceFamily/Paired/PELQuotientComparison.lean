import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionQuotientComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELFunctor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELSourceIso

/-! # PEL Quotient Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotientComparison

noncomputable section

/-! An actual source PEL isomorphism carrying one full kernel to the
other extends to an isomorphism of paired quotients on arbitrary tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))}
    {A B A' B' : PEL.Objects.PELObject P iota N T}

def pairedPELQuotientIsoOfKernel
    (f : PELQuotients.PairedPELQuotient A B n) (g : PELQuotients.PairedPELQuotient A' B' n)
    (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
    (e : PEL.Objects.PELIso A A')
    (hk : ∀ (X : Over T.left) (x : X ⟶ A.polarized.abelian.scheme),
      x ≫ f.forward.isogeny.hom = 1 ↔
        (x ≫ e.polarized.abelian.hom) ≫ g.forward.isogeny.hom = 1) :
    PELFunctor.PairedPELQuotientIso f g := by
  let r := g.forward.precompose e
  have hker : Isogenies.NeighborCounting.QuotientComparison.SameKernel f.forward.isogeny r.isogeny := by
    intro X x
    exact (hk X x).trans (g.forward.precompose_kernel e X x).symm
  let d := UniversalFunctionQuotientComparison.universalFunctionQuotientPELIso A B B' hA f.forward.isogeny r.isogeny hker
    (f.forward.polarization.trans r.polarization.symm) f.forward.action r.action
    f.forward.marking r.marking
  exact {
    source := e
    target := d
    forward_square := UniversalFunctionQuotientComparison.universalFunctionQuotientPELIso_projection A B B' hA
      f.forward.isogeny r.isogeny hker (f.forward.polarization.trans r.polarization.symm)
      f.forward.action r.action f.forward.marking r.marking }

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotientComparison
