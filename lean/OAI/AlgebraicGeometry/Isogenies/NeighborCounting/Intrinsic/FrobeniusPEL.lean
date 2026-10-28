import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.KernelBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricMarking

/-! # Frobenius PEL -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusPEL

noncomputable section

/-! The actual native Frobenius has a complete positive marked PEL
quotient witness into the source pullback, with its original morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}

def nativeFrobeniusPEL (A : D.GeometricPELDatum) :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (QuotientTargets.geometricFamily A)
      (QuotientTargets.geometricFamily (A.pullback D.nativeIntegralGeometricFrobenius)) q :=
  let A0 : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * (s + 1)) (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) :=
    A.data.polarized.abelian
  let sF := Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q))
  let AF := A0.pullback sF
  let f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A0 AF := AbelianScheme.FrobeniusKernel.Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q)) A0
  letI : GrpObj A0.scheme := A0.group
  letI : GrpObj AF.scheme := AF.group
  letI : IsMonHom f.hom := f.preservesGroup
  let H : Grp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)))) := Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f.hom)
  let i : H.X ⟶ A0.scheme := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f.hom
  let hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f.hom i := AbelianScheme.FrobeniusKernel.KernelBaseChange.Construction.nativeKernel_prescribed f.hom
  QuotientTargets.witnessIsogeny (D.frobeniusQuotientWitness A H i hi)

theorem nativeFrobeniusPEL_hom (A : D.GeometricPELDatum) :
    (nativeFrobeniusPEL A).isogeny.hom =
      (AbelianScheme.FrobeniusKernel.Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q))
        A.data.polarized.abelian).hom := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusPEL
