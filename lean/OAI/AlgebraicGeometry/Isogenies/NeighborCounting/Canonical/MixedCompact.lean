import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeCompactPowers
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel

/-! # Mixed Compact -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedCompact

noncomputable section

/-! Every compact chosen and opposite restriction of X followed by an
independently specified canonical ordinary quotient is computed from the
two original complete kernels. The canonical target pairing and its
nondegeneracy follow from the actual polarization and Rosati condition. The total multiplier is q^(m+1). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OneStepKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusKernelComparison.IntrinsicCompact
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OrdinaryFamilies.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeCompactPowers OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [IsAlgClosed k] [CharP k q] {d N : ℕ} {δ : Fin d → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (compact : Fin s → Bool)
variable (e : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) 1) q 1
    (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact v))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

variable (m : ℕ)
variable (H0 : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (0, false)) m))
variable (C0 : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (v.succ, false)) m))
variable (hC0 : ∀ (v : Fin s) (T : Over (Spec (.of k)))
  (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (v.succ, false)) m).X),
  (∃ h : T ⟶ (C0 v).group.X, h ≫ (C0 v).inclusion.hom.hom = a) ↔ if compact v then True else a = 1)
variable (hρF : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ))
variable (hdegree : q.Coprime (∏ i, δ i))
variable (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable {C : Over (Spec (.of k))} [GrpObj C]
variable (g : (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme ⟶ C) [IsMonHom g]
variable (hg : ∀ (T : Over (Spec (.of k))) (a : T ⟶ (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme),
  a ≫ g = 1 ↔ AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) m (s + 1) labels
    (OrdinaryFamilies.Ordinary.canonicalChosenFamily j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) m s labels H0 C0) T a)

include e hdual hC0 hg in
omit [NumberField.IsCMField E] in
theorem canonical_mixed_compact_chosen {n : ℕ} (h1n : 1 ≤ n) (hmn : m ≤ n) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit n (labels (v.succ, false))) = a) :
    a ≫ ((AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g) = 1 ↔
      if compact v then a ^ (q ^ (m + 1)) = 1 else a = 1 := by
  have : IsMonHom (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom :=
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).preservesGroup
  let τ := labels (v.succ, false)
  let p := ρ.map (j.projector iota hsplit n τ)
  let r := (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ).map (j.projector iota hsplit n τ)
  have hs : p ≫ (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom =
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ r :=
    (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q Fact.out
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))).naturality p
  have hc := @CompositeCompactPowers.composite_compact_kernel (Spec (.of k)) PEL.abelian.scheme
    (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme C PEL.abelian.group
    (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.group inferInstance
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).preservesGroup g p inferInstance r hs q (q ^ m) (compact v)
    (fun U b hb => Intrinsic.FrobeniusKernelComparison.IntrinsicCompact.native_frobenius_compact_chosen j iota hsplit PEL ρ s labels compact e hdual
      h1n v U b hb)
    (fun U b hb => OneStepKernel.canonical_one_step_compact_chosen j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) m s labels compact H0 C0 hC0
      g hg hmn v U b hb) T a ha
  change (a ≫ ((AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g) = 1 ↔
    if compact v then a ^ (q ^ m * q) = 1 else a = 1) at hc
  rw [← Nat.pow_succ] at hc
  exact hc

include e hdual hC0 hg hρF hdegree hc in
theorem canonical_mixed_compact_opposite {n : ℕ} (h1n : 1 ≤ n) (hmn : m ≤ n) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit n (labels (v.succ, true))) = a) :
    a ≫ ((AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g) = 1 ↔
      if compact v then a = 1 else a ^ (q ^ (m + 1)) = 1 := by
  have : IsMonHom (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom :=
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).preservesGroup
  let τ := labels (v.succ, true)
  let p := ρ.map (j.projector iota hsplit n τ)
  let r := (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ).map (j.projector iota hsplit n τ)
  have hs : p ≫ (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom =
      (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ r :=
    (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q Fact.out
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))).naturality p
  have hc := @CompositeCompactPowers.composite_compact_kernel (Spec (.of k)) PEL.abelian.scheme
    (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.scheme C PEL.abelian.group
    (Intrinsic.XYActiveKernel.frobeniusPEL k PEL).abelian.group inferInstance
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).preservesGroup g p inferInstance r hs q (q ^ m) (!compact v)
    (fun U b hb => by
      have h := Intrinsic.FrobeniusKernelComparison.IntrinsicCompact.native_frobenius_compact_opposite j iota hsplit PEL ρ s labels compact e hdual
        h1n v U b hb
      cases hb : compact v <;> rw [hb] at h <;> exact h)
    (fun U b hb => by
      have h := OneStepKernel.canonical_one_step_compact_opposite j iota hsplit (Intrinsic.XYActiveKernel.frobeniusPEL k PEL)
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) m s labels compact H0 C0 hC0
        g hg hρF hdegree hc hmn v U b hb
      cases hb : compact v <;> rw [hb] at h <;> exact h) T a ha
  change (a ≫ ((AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g) = 1 ↔
    if !compact v then a ^ (q ^ m * q) = 1 else a = 1) at hc
  cases hb : compact v
  · simpa only [hb, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Nat.pow_succ] using hc
  · simpa only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.pow_succ] using hc

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.MixedCompact
