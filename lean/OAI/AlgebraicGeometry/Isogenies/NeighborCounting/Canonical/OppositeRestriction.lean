import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.BlockPairing
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

/-! # Opposite Restriction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OppositeRestriction

noncomputable section

/-! Exact opposite restriction of the canonical quotient kernel as the
actual relative annihilator in the original coefficient block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.BlockPairing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Opposite

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

abbrev originalBlockPoint (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :=
  (PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T)
    ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) a)

omit [IsAlgClosed k] in
theorem originalBlockPoint_val (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (originalBlockPoint j iota hsplit A ρ n τ T a).val =
      a ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ := rfl

omit [IsAlgClosed k] in
theorem originalBlockPoint_fixed (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (originalBlockPoint j iota hsplit A ρ n τ T a).val ≫
      ρ.map (j.projector iota hsplit n τ) = (originalBlockPoint j iota hsplit A ρ n τ T a).val :=
  PELModuli.CMPoints.BlockDecomposition.block_projector_self j iota hsplit A.abelian ρ n τ T
    ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T) a)

omit [IsAlgClosed k] in
theorem originalBlockPoint_natural (n : ℕ) (τ : Gal(E/ℚ)) {T U : Over (Spec (.of k))}
    (t : U ⟶ T) (a : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X) :
    (A.abelian.torsionFunctor (q ^ n)).map t.op (originalBlockPoint j iota hsplit A ρ n τ T a) =
      originalBlockPoint j iota hsplit A ρ n τ U (t ≫ a) := by
  apply Subtype.ext
  exact (Category.assoc t a (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ)).symm

variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem prescribed_full_kernel_opposite_annihilator {P : Over (Spec (.of k))}
    (v : Fin s) (T : Over (Spec (.of k))) (t : T ⟶ P)
    (b : T ⟶ (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, true)) n).X) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T
      (b ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, true))) ↔
      b ∈ ((BlockPairing.prescribedOriginalBlockPairing j iota hsplit A ρ n
        (labels (v, false)) (labels (v, true))).relativeAnnihilator
          (Kernel.Base.fixedKernelFamily (P := P) (H v).inclusion.hom.hom)).points T t := by
  have he := PrescribedKernelOf.Opposite.prescribed_full_kernel_on_opposite j iota hsplit A ρ n s labels H v T
    (originalBlockPoint j iota hsplit A ρ n (labels (v, true)) T b)
    (originalBlockPoint_fixed j iota hsplit A ρ n (labels (v, true)) T b)
  refine he.trans ?_
  constructor
  · intro ho U u a ha
    obtain ⟨h, hh⟩ := ha
    change h ≫ (H v).inclusion.hom.hom = a at hh
    subst a
    have hp := ho U u h
    rw [originalBlockPoint_natural] at hp
    exact (BlockPairing.canonicalTorsionOrthogonal_original_blocks j iota hsplit A ρ n
      (labels (v, false)) (labels (v, true)) U (h ≫ (H v).inclusion.hom.hom) (u ≫ b)).mp hp
  · intro ho U u h
    rw [originalBlockPoint_natural]
    apply (BlockPairing.canonicalTorsionOrthogonal_original_blocks j iota hsplit A ρ n
      (labels (v, false)) (labels (v, true)) U (h ≫ (H v).inclusion.hom.hom) (u ≫ b)).mpr
    exact ho U u (h ≫ (H v).inclusion.hom.hom) ⟨h, rfl⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OppositeRestriction
