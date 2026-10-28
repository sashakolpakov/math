import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessConstruction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomomorphismsScaling

/-! # Quotient Witness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
Construct a complete PEL quotient witness for the actual Frobenius
kernel. The target retains polarization, the integral action, full
marking, Rosati and Lie conditions by genuine base change.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem QuotientWitness.Construction.geometricBaseFrobenius_hom_left (q : ℕ) [Fact q.Prime] :
    (ModuliPoint.Construction.geometricBaseFrobenius q).hom.left =
      Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (.of (ModuliPoint.Construction.residueClosure q)))
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)) := by
  rw [Picard.Homomorphisms.Affine.Construction.absoluteFrobenius_spec q (Fact.out : q.Prime) (ModuliPoint.Construction.residueClosure q)
    (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)]
  change Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquiv (ZMod q) (ModuliPoint.Construction.residueClosure q) q).toRingHom) = _
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change a ^ Fintype.card (ZMod q) = a ^ q
  rw [ZMod.card]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

theorem Integral.Construction.SplitPELReduction.integralGeometricFrobenius_left : D.integralGeometricFrobenius.left =
    Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) D.integralGeometricBase.left
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)) :=
  FrobeniusKernel.QuotientWitness.Construction.geometricBaseFrobenius_hom_left q

/-- The same arithmetic-base morphism, with its native scheme Frobenius
presentation exposed for the quotient construction. -/
def Integral.Construction.SplitPELReduction.nativeIntegralGeometricFrobenius : D.integralGeometricBase ⟶ D.integralGeometricBase :=
  Over.homMk
    (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) D.integralGeometricBase.left
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q)))
    (by rw [← D.integralGeometricFrobenius_left]; exact D.integralGeometricFrobenius.w)

theorem Integral.Construction.SplitPELReduction.nativeIntegralGeometricFrobenius_eq :
    D.nativeIntegralGeometricFrobenius = D.integralGeometricFrobenius :=
  Over.OverMorphism.ext D.integralGeometricFrobenius_left.symm

/-- The complete target PEL object and every quotient equation are
constructed once the prescribed embedded kernel has been identified. -/
def Integral.Construction.SplitPELReduction.frobeniusQuotientWitness (source : D.GeometricPELDatum)
    (H : Grp (Over D.integralGeometricBase.left)) (i : H.X ⟶ source.data.polarized.abelian.scheme)
    (hkernel : Prescribed.Construction.PrescribedKernel
      (Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))
        source.data.polarized.abelian).hom i) : D.QuotientWitness source q H i where
  target := source.pullback D.nativeIntegralGeometricFrobenius
  isogeny := Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))
    source.data.polarized.abelian
  kernel := hkernel
  polarization := HomomorphismsScaling.Construction.e57NativeSource_polarization_pullback q (ModuliPoint.Construction.residueClosure q)
    source.data.polarized.dual source.data.polarized.polarization
  action := Action.Construction.relativeFrobenius_action_intertwines q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))
    source.data.action
  marking T c := FrobeniusLevel.Construction.relativeFrobenius_transports_level q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q (ModuliPoint.Construction.residueClosure q) (CharP.cast_eq_zero (ModuliPoint.Construction.residueClosure q) q))
    source.data.polarized.level T.unop c

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
