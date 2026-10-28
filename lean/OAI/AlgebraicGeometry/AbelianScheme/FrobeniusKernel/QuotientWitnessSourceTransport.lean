import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessConstruction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardGroupMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.FamilyTransport

/-! # Quotient Witness Source Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! A native isomorphism of the original polarized and marked source
transports a complete quotient witness. The target is retained and
every source, kernel, multiplier, action and marking equation is proved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable {D : Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {source source' : D.GeometricPELDatum} {m : ℕ}
variable {H H' : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ source.data.polarized.abelian.scheme}
variable (i' : H'.X ⟶ source'.data.polarized.abelian.scheme)

def Integral.Construction.SplitPELReduction.QuotientWitness.sourceTransportIsogeny (Q : D.QuotientWitness source m H i)
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso source'.data source.data) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny source'.data.polarized.abelian Q.target.data.polarized.abelian := by
  have : IsMonHom e.polarized.abelian.symm.hom := inferInstanceAs (IsMonHom e.polarized.abelian.inv)
  exact Q.isogeny.familyTransport e.polarized.abelian.symm

theorem Integral.Construction.SplitPELReduction.QuotientWitness.sourceTransportIsogeny_hom (Q : D.QuotientWitness source m H i)
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso source'.data source.data) :
    (Q.sourceTransportIsogeny e).hom = e.polarized.abelian.hom ≫ Q.isogeny.hom := rfl

theorem Integral.Construction.SplitPELReduction.QuotientWitness.sourceTransport_polarization (Q : D.QuotientWitness source m H i)
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso source'.data source.data) :
    PolarizationComparison.Construction.polarizationPullbackHom (Q.sourceTransportIsogeny e).hom source'.data.polarized.dual
      Q.target.data.polarized.dual Q.target.data.polarized.polarization =
        source'.data.polarized.polarization.isogeny.hom ^ m := by
  change PolarizationComparison.Construction.polarizationPullbackHom (e.polarized.abelian.hom ≫ Q.isogeny.hom)
    source'.data.polarized.dual Q.target.data.polarized.dual Q.target.data.polarized.polarization = _
  exact SourceTransport.Construction.polarizationPullbackHom_sourceIso e.polarized Q.isogeny
    Q.target.data.polarized.dual Q.target.data.polarized.polarization m Q.polarization

def Integral.Construction.SplitPELReduction.QuotientWitness.transportSource (Q : D.QuotientWitness source m H i)
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso source'.data source.data) (eH : H'.X ≅ H.X)
    (he : i' ≫ e.polarized.abelian.hom = eH.hom ≫ i) :
    D.QuotientWitness source' m H' i' where
  target := Q.target
  isogeny := Q.sourceTransportIsogeny e
  kernel := SourceTransport.Construction.prescribedKernel_transport Q.isogeny.hom i i' e.polarized.abelian eH he Q.kernel
  polarization := Q.sourceTransport_polarization e
  action a := by
    change source'.data.action.map a ≫ (e.polarized.abelian.hom ≫ Q.isogeny.hom) =
      (e.polarized.abelian.hom ≫ Q.isogeny.hom) ≫ Q.target.data.action.map a
    rw [← Category.assoc, e.action a, Category.assoc, Q.action a, Category.assoc]
  marking T c := by
    change (Q.target.data.polarized.level.hom.app T c).val =
      (source'.data.polarized.level.hom.app T c).val ≫ (e.polarized.abelian.hom ≫ Q.isogeny.hom)
    rw [Q.marking, ← e.polarized.level T.unop c, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
