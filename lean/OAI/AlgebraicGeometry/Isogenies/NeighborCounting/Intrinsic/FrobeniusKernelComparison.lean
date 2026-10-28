import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepCompactKernel
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplitting

/-! # Frobenius Kernel Comparison -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusKernelComparison.IntrinsicX

/-! Identify the original full X inclusion with the level-one native
chosen/opposite construction. The only level transport is q^1=q;
the original subgroup, Cartier pairing and ambient inclusion are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction

theorem fullKernelToAbelian_level_transport {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {m n : ℕ} (h : m = n)
    (s : ℕ) (H B : Fin s → Grp (Over S)) (i : ∀ v, H v ⟶ B v)
    (split : AbelianScheme.FrobeniusKernel.Assembly.Construction.torsionGroup A m ≅ AbelianScheme.FrobeniusKernel.BlockProducts.Construction.groupBlockProduct s B) :
    AbelianScheme.FrobeniusKernel.Assembly.Construction.fullKernelToAbelian A n s H B i
      (eqToIso (congrArg (AbelianScheme.FrobeniusKernel.Assembly.Construction.torsionGroup A) h.symm) ≪≫ split) =
    AbelianScheme.FrobeniusKernel.Assembly.Construction.fullKernelToAbelian A m s H B i split := by
  cases h
  simp only [eqToIso_refl, Iso.refl_trans]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] [CharP k q]
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))
variable (d r : Fin s → ℕ)
variable (e : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 (labels (v, false))).toGrp
    q 1 (d v) (r v))

omit [IsAlgClosed k] [CharP k q] in
theorem native_X_inclusion_eq :
    AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction.l45FullXKernelInclusion j iota hsplit PEL ρ s labels hdual d r e =
    AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ 1 s labels
      (fun v => AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockCoordinates j iota hsplit PEL ρ (labels (v, false)) (e v))
      (fun v => AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e v)) hdual :=
  fullKernelToAbelian_level_transport PEL.abelian (pow_one q) s
    (fun v => (AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction.l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).kernel)
    (fun v => (AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction.l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).chosen ⊗
      (AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction.l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).opposite)
    (fun v => (AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction.l45OrdinaryPairedFamily j iota hsplit PEL ρ s labels hdual d r e v).inclusion)
    (AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit PEL.abelian ρ 1 s labels)

theorem native_X_kernel :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (AbelianScheme.FrobeniusKernel.Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ 1 s labels
        (fun v => AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockCoordinates j iota hsplit PEL ρ (labels (v, false)) (e v))
        (fun v => AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e v)) hdual) := by
  rw [← native_X_inclusion_eq j iota hsplit PEL ρ s labels hdual d r e]
  exact AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction.l45FullXKernel_frobeniusKernel j iota hsplit PEL ρ s labels hdual d r e

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusKernelComparison.IntrinsicX

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusKernelComparison.IntrinsicCompact

/-! The original abelian Frobenius has its full compact restrictions
computed from the native X kernel, at every higher coefficient level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsSplitting.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepCompactKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusKernelComparison.IntrinsicX

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] [CharP k q] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (compact : Fin s → Bool)
variable (e : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) 1) q 1
    (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact v))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

omit [IsAlgClosed k] [CharP k q] in
theorem ordinary_multiplicative_family :
    (fun v => AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e v)) =
      OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ 1 s labels compact e (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e 0)) := by
  funext v
  exact Fin.cases rfl (fun _ => rfl) v

theorem native_frobenius_ordinary_kernel :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (AbelianScheme.FrobeniusKernel.Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom
      (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ 1 (s + 1) labels
        (fun v => AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockCoordinates j iota hsplit PEL ρ (labels (v, false)) (e v))
        (OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ 1 s labels compact e
          (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e 0))) hdual) := by
  rw [← ordinary_multiplicative_family j iota hsplit PEL ρ s labels compact e]
  exact IntrinsicX.native_X_kernel j iota hsplit PEL ρ (s + 1) labels hdual
    (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact) e

include e hdual in
theorem native_frobenius_compact_chosen {n : ℕ} (hn : 1 ≤ n) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit n (labels (v.succ, false))) = a) :
    a ≫ (AbelianScheme.FrobeniusKernel.Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom = 1 ↔
      if compact v then a ^ q = 1 else a = 1 := by
  simpa only [pow_one] using OneStepCompactKernel.native_one_step_compact_chosen j iota hsplit PEL ρ 1 s labels compact e
    (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e 0))
    (fun v => AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockCoordinates j iota hsplit PEL ρ (labels (v, false)) (e v)) hdual
    (AbelianScheme.FrobeniusKernel.Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom
    (native_frobenius_ordinary_kernel j iota hsplit PEL ρ s labels compact e hdual) hn v T a ha

include e hdual in
theorem native_frobenius_compact_opposite {n : ℕ} (hn : 1 ≤ n) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ PEL.abelian.scheme)
    (ha : a ≫ ρ.map (j.projector iota hsplit n (labels (v.succ, true))) = a) :
    a ≫ (AbelianScheme.FrobeniusKernel.Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom = 1 ↔
      if compact v then a = 1 else a ^ q = 1 := by
  simpa only [pow_one] using OneStepCompactKernel.native_one_step_compact_opposite j iota hsplit PEL ρ 1 s labels compact e
    (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e 0))
    (fun v => AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockCoordinates j iota hsplit PEL ρ (labels (v, false)) (e v)) hdual
    (AbelianScheme.FrobeniusKernel.Torsion.Construction.geometricFrobeniusIsogeny q k PEL.abelian).hom
    (native_frobenius_ordinary_kernel j iota hsplit PEL ρ s labels compact e hdual) hn v T a ha

end AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.FrobeniusKernelComparison.IntrinsicCompact

end

end OAI
