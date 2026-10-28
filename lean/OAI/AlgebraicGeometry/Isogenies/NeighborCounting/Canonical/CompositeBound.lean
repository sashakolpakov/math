import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedCompact
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricMarking

/-! # Composite Bound -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompositeBound

noncomputable section

/-! The complete Frobenius composite is killed by the literal product
of its two kernel bounds. This all-test bound constructs the actual
complementary isogeny map; it is not an extra kernel hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricMarking.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel

theorem composite_kernel_bound {S : Scheme} {A B C : Over S}
    [GrpObj A] [GrpObj B] [GrpObj C] (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C)
    (m n : ℕ)
    (hf : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ^ m = 1)
    (hg : ∀ (T : Over S) (b : T ⟶ B), b ≫ g = 1 → b ^ n = 1)
    (T : Over S) (a : T ⟶ A) (ha : a ≫ f ≫ g = 1) : a ^ (n * m) = 1 := by
  have hfg := hg T (a ≫ f) ((Category.assoc _ _ _).trans ha)
  have hf' : (a ^ n) ≫ f = 1 := (MonObj.pow_comp a n f).trans hfg
  exact (pow_mul a n m).trans (hf T (a ^ n) hf')

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [IsAlgClosed k] [CharP k q] {d N : ℕ} {δ : Fin d → ℕ}
variable (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
variable (m s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PA)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ) (labels (v, false)) m))
variable {C : Over (Spec (.of k))} [GrpObj C]
variable (g : (Intrinsic.XYActiveKernel.frobeniusPEL k PA).abelian.scheme ⟶ C)
variable (hg : ∀ (T : Over (Spec (.of k))) (a : T ⟶ (Intrinsic.XYActiveKernel.frobeniusPEL k PA).abelian.scheme),
  a ≫ g = 1 ↔ AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PA)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ) m s labels H T a)

include hg in
theorem canonical_frobenius_composite_bound (T : Over (Spec (.of k))) (a : T ⟶ PA.abelian.scheme)
    (ha : a ≫ (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).hom ≫ g = 1) :
    a ^ (q ^ (m + 1)) = 1 := by
  have h := @composite_kernel_bound (Spec (.of k)) PA.abelian.scheme
    (Intrinsic.XYActiveKernel.frobeniusPEL k PA).abelian.scheme C PA.abelian.group (Intrinsic.XYActiveKernel.frobeniusPEL k PA).abelian.group inferInstance
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).hom
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PA.abelian).preservesGroup g q (q ^ m)
    (AbelianScheme.FrobeniusKernel.GeometricMarking.Construction.geometricFrobenius_kernel_killed q k PA.abelian)
    (fun U b hb => PrescribedKernelOf.Components.prescribed_full_kernel_killed j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PA)
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PA.abelian ρ) m s labels H U b ((hg U b).mp hb)) T a ha
  simpa only [Nat.pow_succ] using h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CompositeBound
