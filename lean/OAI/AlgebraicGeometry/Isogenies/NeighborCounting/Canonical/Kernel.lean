import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedBlockCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Kernel

noncomputable section

/-! Reconstruct the complete canonical kernel from every original
chosen block and its actual polarization annihilator. The proof uses
the original integral projectors and all scheme-valued points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.BlockPairing OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.OppositeRestriction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Containment OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedBlockCoordinates

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

def originalCanonicalFullFamily {P : Over (Spec (.of k))} :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.abelian.scheme P :=
  AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct
    (Kernel.Base.fixedKernelFamily ((H v).inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))))
    (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, true)))
      ((BlockPairing.prescribedOriginalBlockPairing j iota hsplit A ρ n
        (labels (v, false)) (labels (v, true))).relativeAnnihilator
          (Kernel.Base.fixedKernelFamily (H v).inclusion.hom.hom))))

theorem originalCanonicalFullFamily_baseChange {P Q : Over (Spec (.of k))} (b : Q ⟶ P) :
    (originalCanonicalFullFamily (P := P) j iota hsplit A ρ n s labels H).baseChange b =
      originalCanonicalFullFamily (P := Q) j iota hsplit A ρ n s labels H := by
  unfold originalCanonicalFullFamily
  rw [AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel_baseChange]
  congr 1

/-- Any realization of the independently specified canonical predicate
has this full chosen/annihilator product, with all embeddings retained. -/
theorem prescribed_full_family_eq {P : Over (Spec (.of k))}
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.abelian.scheme P)
    (hF : ∀ (T : Over (Spec (.of k))) (t : T ⟶ P) (a : T ⟶ A.abelian.scheme),
      a ∈ F.points T t ↔ AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a) :
    F = originalCanonicalFullFamily j iota hsplit A ρ n s labels H := by
  ext T t a
  rw [originalCanonicalFullFamily, TupleKernelPoints.tupleKernel_mem_iff]
  constructor
  · intro ha
    obtain ⟨x, hx, hp⟩ := (hF T t a).mp ha
    refine ⟨fun v =>
      (x.val ≫ ρ.map (j.projector iota hsplit n (labels (v, false)))) *
      (x.val ≫ ρ.map (j.projector iota hsplit n (labels (v, true)))), ?_,
      (PrescribedBlockCoordinates.prescribed_components_product j iota hsplit A ρ n s labels T x).trans hx⟩
    intro v
    refine ⟨_, ?_, _, ?_, rfl⟩
    · obtain ⟨h, hh⟩ := (hp v).1
      refine ⟨h, ?_⟩
      have he := congrArg Subtype.val hh
      rw [PrescribedKernelOf.Components.prescribedChosenPoint_val, PrescribedKernelOf.Components.prescribedBlockComponent_val] at he
      exact he
    · exact ⟨PrescribedBlockCoordinates.prescribedBlockRepresentative j iota hsplit A ρ n (labels (v, true)) T x,
        PrescribedBlockCoordinates.prescribed_opposite_representative_mem j iota hsplit A ρ n s labels H T t x
          (fun w => (hp w).2) v,
        PrescribedBlockCoordinates.prescribedBlockRepresentative_inclusion j iota hsplit A ρ n (labels (v, true)) T x⟩
  · rintro ⟨b, hb, hprod⟩
    rw [← hprod]
    apply (F.points T t).prod_mem
    intro v _
    obtain ⟨c, hc, o, ho, hco⟩ := hb v
    rw [hco]
    apply (F.points T t).mul_mem
    · obtain ⟨h, hh⟩ := hc
      change h ≫ (H v).inclusion.hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false)) = c at hh
      apply (hF T t c).mpr
      rw [← hh]
      exact PrescribedKernelOf.Containment.prescribed_full_kernel_contains_chosen j iota hsplit A ρ n s labels H v T h
    · obtain ⟨h, hh, hi⟩ := ho
      change h ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, true)) = o at hi
      apply (hF T t o).mpr
      rw [← hi]
      exact (OppositeRestriction.prescribed_full_kernel_opposite_annihilator j iota hsplit A ρ n s labels H v T t h).mpr hh

variable [NumberField.IsCMField E] {r : ℕ} {PEL : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (r + 1)}
variable {arithmeticEmbedding : E →+* K}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject PEL arithmeticEmbedding N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}
variable (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction PEL arithmeticEmbedding κ M U B q)
variable {x y : D.OrdinaryPoint} {multiplier : ℕ}
variable (nativeLabels : (Fin (r + 1) × Bool) ≃ Gal(E/ℚ))
variable (HH : ∀ v : Fin (r + 1), AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action (nativeLabels (v, false)) n))
variable (Q : D.PrescribedOrdinaryQuotient x multiplier
  (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action n (r + 1) nativeLabels HH) y)

def quotientCanonicalKernelFamily {Ptest : Over D.integralGeometricBase.left} :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (D.pointDatum x.val).data.polarized.abelian.scheme Ptest := by
  let := Q.preservesGroup
  exact Kernel.Base.fixedKernelFamily Q.inclusion

/-- Apply the reconstruction to the actual full PEL quotient supplied
by FrobeniusKernel. The complete chosen/annihilator comparison is a conclusion. -/
theorem canonical_quotient_full_family_eq {Ptest : Over D.integralGeometricBase.left} :
    quotientCanonicalKernelFamily j iota hsplit n D nativeLabels HH Q =
      originalCanonicalFullFamily (P := Ptest) j iota hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action n (r + 1) nativeLabels HH := by
  apply prescribed_full_family_eq j iota hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action n (r + 1) nativeLabels HH
  intro T _ a
  exact Q.realizes T a

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.Kernel
