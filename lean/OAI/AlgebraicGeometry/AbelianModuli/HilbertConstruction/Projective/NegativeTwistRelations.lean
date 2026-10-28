import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.NegativeTwistCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Negative Twist Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! The constructed negative-twist quotient has an actual quasicoherent finite-type relation sheaf and a short exact sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
    {I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)} {M : (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules}

def NegativeTwistCover.ProjectiveNegativeTwistCover.relations (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M) : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules :=
  kernel D.projection

theorem NegativeTwistCover.ProjectiveNegativeTwistCover.relations_quasicoherent (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M) [M.IsQuasicoherent] :
    D.relations.IsQuasicoherent := by
  rename_i hMq
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : D.source.IsQuasicoherent := D.source_quasicoherent
  exact Quasicoherent.Kernels.module_quasicoherent_kernel D.projection

theorem NegativeTwistCover.ProjectiveNegativeTwistCover.relations_finiteType [IsNoetherianRing R]
    (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M) [M.IsQuasicoherent] : D.relations.IsFiniteType := by
  rename_i hMq
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let : M.IsQuasicoherent := hMq
  let : D.source.IsQuasicoherent := D.source_quasicoherent
  let : D.source.IsFiniteType := D.source_finiteType
  let : IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) := HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper I
  let : IsLocallyNoetherian (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) :=
    LocallyOfFiniteType.isLocallyNoetherian (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
  exact Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType D.projection

def NegativeTwistCover.ProjectiveNegativeTwistCover.relationSequence (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M) :
    ShortComplex (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules :=
  ShortComplex.mk (kernel.ι D.projection) D.projection (kernel.condition D.projection)

theorem NegativeTwistCover.ProjectiveNegativeTwistCover.relationSequence_shortExact (D : NegativeTwistCover.ProjectiveNegativeTwistCover I M) :
    D.relationSequence.ShortExact := by
  change (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at M
  have hm : Mono (kernel.ι D.projection) := inferInstance
  exact ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact D.projection) hm D.projection_epi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
