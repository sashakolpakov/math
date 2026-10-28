import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointQuotientWitness
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.ComparisonFromChosen

/-! # PEL Chosen Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PELChosenComparison

noncomputable section

/-! Full geometric PEL isogenies with equal chosen components have the
same complete kernel, retaining the actual positive Poincare pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.ComparisonFromChosen

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {A B₁ C : D.GeometricPELDatum} {n : ℕ}
  (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily B₁) (q ^ n))
  (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (Intrinsic.QuotientTargets.geometricFamily A) (Intrinsic.QuotientTargets.geometricFamily C) (q ^ n))

theorem geometricIsogeny_native_polarization :
    AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.isogeny.hom A.data.polarized.dual
      B₁.data.polarized.dual B₁.data.polarized.polarization =
        A.data.polarized.polarization.isogeny.hom ^ (q ^ n) := by
  have h := f.polarization
  rw [PolarizedComparison.pel_dualMap, Intrinsic.DualIdentification.dualMap_eq_native] at h
  exact h

theorem geometricIsogeny_native_action (r : NumberField.RingOfIntegers E) :
    A.data.action.map r ≫ f.isogeny.hom = f.isogeny.hom ≫ B₁.data.action.map r := by
  have h := f.equivariant r
  rw [Intrinsic.QuotientTargets.geometricFamily_action, Intrinsic.QuotientTargets.geometricFamily_action] at h
  exact h

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ v : Fin s, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (hfbound : ∀ (T : Over D.integralGeometricBase.left) (a : T ⟶ A.data.polarized.abelian.scheme),
    a ≫ f.isogeny.hom = 1 → a ^ (q ^ n) = 1)
  (hgbound : ∀ (T : Over D.integralGeometricBase.left) (a : T ⟶ A.data.polarized.abelian.scheme),
    a ≫ g.isogeny.hom = 1 → a ^ (q ^ n) = 1)
  (hchosen : ∀ (v : Fin s) (T : Over D.integralGeometricBase.left)
    (x : (A.data.polarized.abelian.torsionFunctor (q ^ n)).obj (.op T)),
    x.val ≫ A.data.action.map (j.projector iota hsplit n (labels (v, false))) = x.val →
      (x.val ≫ f.isogeny.hom = 1 ↔ x.val ≫ g.isogeny.hom = 1))

include hlabels hfbound hgbound hchosen in
theorem geometricPEL_full_kernel_eq_from_chosen
    (T : Over D.integralGeometricBase.left) (a : T ⟶ A.data.polarized.abelian.scheme) :
    a ≫ f.isogeny.hom = 1 ↔ a ≫ g.isogeny.hom = 1 :=
  Kernel.ComparisonFromChosen.full_kernel_eq_from_chosen j iota hsplit A.data.polarized B₁.data.polarized C.data.polarized
    A.data.action B₁.data.action C.data.action A.rosati f.isogeny g.isogeny
    (geometricIsogeny_native_action f) (geometricIsogeny_native_action g) n hfbound hgbound
    (geometricIsogeny_native_polarization f) (geometricIsogeny_native_polarization g)
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    s labels hlabels hchosen T a

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PELChosenComparison
