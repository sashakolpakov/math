import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.IntrinsicKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies

/-! # Ordinary Families -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OrdinaryFamilies.Ordinary

noncomputable section

/-! Compute the full canonical ordinary family from the original
all-test compact prescription. Every nonzero compact block stays at
the literal multiplier q^n. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Kernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.IntrinsicKernelComparison.Intrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport.Family

theorem compact_prescription_ambient_family {k : Type} [Field k]
    {B : Grp (Over (Spec (.of k)))} [IsCommMonObj B.X]
    {A P : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    (H : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k B) (i : B.X ⟶ A) [IsMonHom i] (flag : Bool)
    (hH : ∀ (T : Over (Spec (.of k))) (a : T ⟶ B.X),
      (∃ h : T ⟶ H.group.X, h ≫ H.inclusion.hom.hom = a) ↔ if flag then True else a = 1) :
    Kernel.Base.fixedKernelFamily (P := P) (H.inclusion.hom.hom ≫ i) =
      if flag then Kernel.Base.fixedKernelFamily i else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  cases hb : flag
  · simp only [Bool.false_eq_true, ↓reduceIte]
    ext T t a
    change (∃ h, h ≫ (H.inclusion.hom.hom ≫ i) = a) ↔ a = 1
    constructor
    · rintro ⟨h, hh⟩
      have hz := (hH T (h ≫ H.inclusion.hom.hom)).mp ⟨h, rfl⟩
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hz
      exact hh.symm.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ i) hz).trans (MonObj.one_comp i)))
    · rintro rfl
      exact ⟨1, MonObj.one_comp _⟩
  · simp only [↓reduceIte]
    ext T t a
    change (∃ h, h ≫ (H.inclusion.hom.hom ≫ i) = a) ↔ ∃ b, b ≫ i = a
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨h ≫ H.inclusion.hom.hom, (Category.assoc _ _ _).trans hh⟩
    · rintro ⟨b, hb'⟩
      have hm : ∃ h : T ⟶ H.group.X, h ≫ H.inclusion.hom.hom = b :=
        (hH T b).mpr (by simp only [hb, ↓reduceIte])
      obtain ⟨h, hh⟩ := hm
      exact ⟨h, (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ i) hh).trans hb')⟩

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)) (compact : Fin s → Bool)
variable (H0 : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (0, false)) n))
variable (C0 : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v.succ, false)) n))
variable (hC0 : ∀ (v : Fin s) (T : Over (Spec (.of k)))
  (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v.succ, false)) n).X),
  (∃ h : T ⟶ (C0 v).group.X, h ≫ (C0 v).inclusion.hom.hom = a) ↔ if compact v then True else a = 1)

def canonicalChosenFamily : ∀ v : Fin (s + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n) := Fin.cases H0 C0

include hC0 in
omit [IsAlgClosed k] in
theorem canonical_chosen_prescription {P : Over (Spec (.of k))} (v : Fin (s + 1)) :
    Kernel.Base.fixedKernelFamily (P := P)
      ((canonicalChosenFamily j iota hsplit A ρ n s labels H0 C0 v).inclusion.hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))) =
      Kernel.Base.chosenKernel
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n (s + 1) labels w))
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n (s + 1) labels w))
        0 (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit A ρ n s labels H0) v := by
  classical
  refine Fin.cases ?_ (fun w => ?_) v
  · rw [Kernel.Base.chosenKernel, ite_eq_left rfl]
    rfl
  · rw [Kernel.Base.chosenKernel, ite_eq_right (Fin.succ_ne_zero w)]
    change Kernel.Base.fixedKernelFamily
      ((C0 w).inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (w.succ, false))) =
      if compact w then Kernel.Base.fixedKernelFamily
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (w.succ, false)))))
      else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup
    rw [Kernel.FamilyTransport.Family.fixed_iso (P := P)
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (w.succ, false)))))
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (w.succ, false)))
      (Intrinsic.KernelComparison.nativeBlockComparison j iota hsplit A ρ n (labels (w.succ, false)))
      (Intrinsic.KernelComparison.nativeBlockComparison_inclusion j iota hsplit A ρ n (labels (w.succ, false)))]
    exact compact_prescription_ambient_family (C0 w) _ (compact w) (hC0 w)

include hC0 in
theorem canonical_ordinary_full_family {P : Over (Spec (.of k))} :
    Kernel.originalCanonicalFullFamily (P := P) j iota hsplit A ρ n (s + 1) labels
      (canonicalChosenFamily j iota hsplit A ρ n s labels H0 C0) =
      Kernel.Models.multiplierFullKernel (q ^ n)
        (Intrinsic.KernelComparison.chosenProjector j iota hsplit A ρ n (s + 1) labels)
        (Intrinsic.KernelComparison.oppositeProjector j iota hsplit A ρ n (s + 1) labels)
        (fun v => CoefficientPerfection.canonicalCoefficientPairing j iota hsplit A ρ n (labels (v, false)) (labels (v, true)))
        0 (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.compactPrescription s compact) (Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary.activeChosenFamily j iota hsplit A ρ n s labels H0) := by
  rw [IntrinsicKernelComparison.Intrinsic.originalCanonicalFullFamily_native]
  unfold Kernel.Models.multiplierFullKernel Kernel.Base.fullKernel
  congr 1
  funext v
  rw [canonical_chosen_prescription j iota hsplit A ρ n s labels compact H0 C0 hC0 v]
  rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OrdinaryFamilies.Ordinary
