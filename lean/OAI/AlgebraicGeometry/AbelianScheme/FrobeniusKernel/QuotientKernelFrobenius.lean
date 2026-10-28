import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Group

/-! # Quotient Kernel Frobenius -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Full quotient targets commute with Frobenius when their original
kernel predicates do, before specializing the source PEL data to points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable {D : Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {source sourceF : D.GeometricPELDatum} {m : ℕ}
variable {H HF : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ source.data.polarized.abelian.scheme}
variable {iF : HF.X ⟶ sourceF.data.polarized.abelian.scheme}
variable (QF : D.QuotientWitness sourceF m HF iF)
variable (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
  (source.data.pullback
    (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))))
  sourceF.data)
variable (c : PolarizedComponents.Construction.EquivariantAbelianIso
  (CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) (ModuliPoint.Construction.residueClosure q) source.data.polarized.abelian)
  sourceF.data.polarized.abelian
  (CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) (ModuliPoint.Construction.residueClosure q) source.data.polarized.abelian source.data.action)
  sourceF.data.action)
variable (hc : c = PolarizedComponents.Construction.polarizedBaseChangeAbelianComparison source.data sourceF.data
  (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))) e)
variable (P0 : ∀ (T : Over D.integralGeometricBase.left), (T ⟶ source.data.polarized.abelian.scheme) → Prop)
variable (P1 : ∀ (T : Over D.integralGeometricBase.left), (T ⟶ sourceF.data.polarized.abelian.scheme) → Prop)
variable (hP0 : ∀ T a, (∃ h : T ⟶ H.X, h ≫ i = a) ↔ P0 T a)
variable (hP1 : ∀ T a, (∃ h : T ⟶ HF.X, h ≫ iF = a) ↔ P1 T a)
variable (hi : IsClosedImmersion i.left) (hiF : IsClosedImmersion iF.left)
variable (htransport : Embedded.Construction.FrobeniusKernelTransport source.data.polarized.abelian
  sourceF.data.polarized.abelian c.abelian P0 P1)

include hc hP0 hP1 hi hiF htransport in
theorem Integral.Construction.SplitPELReduction.QuotientWitness.frobenius_point_eq_of_kernel_predicate
    (Q : D.QuotientWitness source m H i) (hgood : D.IsGoodCompletelySplitReduction) :
    D.pointOfPEL hgood QF.target = D.frobeniusPoint (D.pointOfPEL hgood Q.target) := by
  obtain ⟨eH, heH⟩ := Group.Construction.exists_frobeniusGroupKernelIso_of_closed
    source.data.polarized.abelian sourceF.data.polarized.abelian H HF i iF c.abelian
    P0 P1 hP0 hP1 hi hiF htransport
  exact QF.frobenius_point_eq_of_comparison e c hc eH heH.symm Q hgood

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
