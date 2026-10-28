import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessConstruction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ClassifyingDataIso

/-! # Quotient Targets -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets

noncomputable section

/-! Compare the actual geometric PEL quotient witnesses and their
classifying points. The source multiplier and kernel equations imply all
target identifications, including positivity, action, and full marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}

abbrev geometricFamily (A : D.GeometricPELDatum) :
    AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) :=
  AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized A.data.polarized (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.data.action)

theorem geometricFamily_action (A : D.GeometricPELDatum) (r : NumberField.RingOfIntegers E) :
    AbelianScheme.TateComparison.End.endSchemeMap (geometricFamily A).abelian.scheme ((geometricFamily A).action r) =
      A.data.action.map r := AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap A.data.action r

variable {A : D.GeometricPELDatum} {m : ℕ}
variable {H : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ A.data.polarized.abelian.scheme}

def witnessIsogeny (Q : D.QuotientWitness A m H i) :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (geometricFamily A) (geometricFamily Q.target) m := by
  let f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (geometricFamily A).abelian
      (geometricFamily Q.target).abelian := Q.isogeny
  refine {
    isogeny := f
    dualHom := DualComparison.dualMap (geometricFamily A).dual (geometricFamily Q.target).dual f.hom
    dualGroup := Dual.dualMap_isMonHom _ _ _
    poincare := ?_
    equivariant := ?_
    polarization := ?_
    marking := fun T c ↦ (Q.marking (.op T) c).symm }
  · simp only [id_tensorHom, tensorHom_id]
    exact PoincareDescent.poincareClass_eq _ _ f.hom
  · intro r
    rw [geometricFamily_action, geometricFamily_action]
    exact Q.action r
  · rw [DualIdentification.dualMap_eq_native]
    exact Q.polarization

def quotientWitnessIso (Q Q' : D.QuotientWitness A m H i) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso Q.target.data Q'.target.data := by
  let f := witnessIsogeny Q
  let g := witnessIsogeny Q'
  have hk : QuotientComparison.SameKernel f.isogeny g.isogeny :=
    fun T a ↦ (Q.kernel T a).trans (Q'.kernel T a).symm
  let e := PELTargetComparison.quotientPELIso f g hk
  refine { polarized := ?_, action := ?_ }
  · exact {
      abelian := e.abelian
      dual := e.dual
      abelianGroup := e.abelianGroup
      dualGroup := e.dualGroup
      polarization := e.polarization
      poincare := e.poincare
      level := e.marking }
  · intro r
    have h := e.equivariant r
    change AbelianScheme.TateComparison.End.endSchemeMap (geometricFamily Q.target).abelian.scheme
        ((geometricFamily Q.target).action r) ≫ e.abelian.hom =
      e.abelian.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap (geometricFamily Q'.target).abelian.scheme
        ((geometricFamily Q'.target).action r) at h
    rw [geometricFamily_action, geometricFamily_action] at h
    exact h

theorem pointOfPEL_eq_of_iso (hgood : D.IsGoodCompletelySplitReduction)
    (A B : D.GeometricPELDatum) (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A.data B.data) :
    D.pointOfPEL hgood A = D.pointOfPEL hgood B := by
  obtain ⟨a⟩ := D.pointOfPEL_classifies hgood A
  exact (D.pointOfPEL_eq_of_pointDatumIso hgood (D.pointOfPEL hgood A) B
    ((a.toActionIso.trans (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackId A.data)).trans e)).symm

theorem quotientWitness_point_eq (hgood : D.IsGoodCompletelySplitReduction)
    (Q Q' : D.QuotientWitness A m H i) :
    D.pointOfPEL hgood Q.target = D.pointOfPEL hgood Q'.target :=
  pointOfPEL_eq_of_iso hgood Q.target Q'.target (quotientWitnessIso Q Q')

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
