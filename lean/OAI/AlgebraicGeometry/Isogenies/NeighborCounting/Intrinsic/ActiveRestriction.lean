import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepKernelRecovery
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Containment

/-! # Active Restriction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveRestriction

noncomputable section

/-! Restrict an independently defined one-step ordinary quotient to an
actual supported subgroup, such as its etale plane. The full kernel
calculation supplies both directions of the restricted kernel identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepKernelRecovery OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Containment

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
variable (compact : Fin s → Bool)
variable (e : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n) q n
    (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact v))
variable (H0 : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (0, false)) n))
variable (P : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of k)
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))
variable {C : Over (Spec (.of k))} [GrpObj C] (f : PEL.abelian.scheme ⟶ C)
variable (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel f
  (AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n (s + 1) labels P
    (OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual))

include hf in
theorem native_one_step_chosen_killed (T : Over (Spec (.of k))) (b : T ⟶ H0.group.X) :
    (b ≫ (H0.inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (0, false)))) ≫ f = 1 := by
  let a := b ≫ (H0.inclusion.hom.hom ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (0, false)))
  have hm := Kernel.Containment.full_kernel_contains_active (q ^ n)
    (KernelComparison.chosenProjector j iota hsplit PEL ρ n (s + 1) labels)
    (KernelComparison.oppositeProjector j iota hsplit PEL ρ n (s + 1) labels)
    (KernelComparison.coefficientPairing j iota hsplit PEL ρ n (s + 1) labels P hdual)
    0 (OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit PEL ρ n s labels H0)
    T (toUnit T) a ⟨b, rfl⟩
  rw [← OrdinaryKernelFamilies.IntrinsicOrdinary.ordinary_full_kernel_family j iota hsplit PEL ρ n s labels compact e H0 P hdual] at hm
  obtain ⟨z, hz⟩ := hm
  change z ≫ AbelianScheme.FrobeniusKernel.CMPointsKernels.Construction.l45FullChosenKernelInclusion j iota hsplit PEL ρ n (s + 1) labels P
    (OrdinaryKernelFamilies.IntrinsicOrdinary.ordinaryChosenFamily j iota hsplit PEL ρ n s labels compact e H0) hdual = a at hz
  change a ≫ f = 1
  rw [← hz, Category.assoc, AbelianScheme.FrobeniusKernel.Prescribed.Construction.prescribedKernel_kills f _ hf, MonObj.comp_one]

include hf in
theorem native_restricted_active_kernel {Et : Over (Spec (.of k))}
    (ein : Et ⟶ PEL.abelian.scheme) [Mono ein] (h : H0.group.X ⟶ Et) [Mono h]
    (hsquare : h ≫ ein = H0.inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit PEL.abelian ρ n (labels (0, false)))
    {m : ℕ} (hnm : n ≤ m)
    (hsupport : ein ≫ ρ.map (j.projector iota hsplit m (labels (0, false))) = ein) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (ein ≫ f) h := by
  intro T a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := OneStepKernelRecovery.native_one_step_active_factor j iota hsplit PEL ρ n s labels compact e H0 P hdual
      f hf hnm T (a ≫ ein) (by rw [Category.assoc, hsupport]) ((Category.assoc _ _ _).trans ha)
    refine ⟨b, (cancel_mono ein).mp ?_, ?_⟩
    · rw [Category.assoc, hsquare]
      exact hb
    · intro c hc
      apply (cancel_mono h).mp
      apply (cancel_mono ein).mp
      rw [hc, Category.assoc, hsquare]
      exact hb.symm
  · rintro ⟨b, rfl, _⟩
    have hk := native_one_step_chosen_killed j iota hsplit PEL ρ n s labels compact e H0 P hdual f hf T b
    rw [← hsquare] at hk
    simpa only [Category.assoc] using hk

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveRestriction
