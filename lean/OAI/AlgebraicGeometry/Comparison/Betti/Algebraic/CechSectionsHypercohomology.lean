import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechHypercohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechSectionsTotal
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.AffineCover

/-! # Cech Sections Hypercohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechSectionsHypercohomology

noncomputable section

/-! The actual Čech–de Rham double complex computes the original algebraic hypercohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsSeparated X.hom]

def finiteAffine_algebraicCechSectionsHypercohomologyEquiv
    {ι : Type} [Finite ι] (U : ι → X.left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤) (n : ℕ) :
    (CechSectionsTotal.algebraicCechSectionsTotalInt X U).homology (n : ℤ) ≃+ Sheaves.algebraicDeRham X n :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (n : ℤ)).mapIso
    (CechSectionsTotal.algebraicCechSectionsTotalIso X U)).addCommGroupIsoToAddEquiv.trans
      (CechHypercohomology.finiteAffine_algebraicCechHypercohomologyEquiv X U hU hcover n)

def smooth_algebraicHypercohomologyCechEquiv [QuasiCompact X.hom] (n : ℕ) :
    (CechSectionsTotal.algebraicCechSectionsTotalInt X (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens X)).homology (n : ℤ) ≃+
      Sheaves.algebraicDeRham X n :=
  finiteAffine_algebraicCechSectionsHypercohomologyEquiv X (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens X)
    (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens_affine X) (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens_cover X) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechSectionsHypercohomology
