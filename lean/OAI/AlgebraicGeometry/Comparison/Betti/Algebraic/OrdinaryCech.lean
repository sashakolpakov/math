import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCechTotal
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechSectionsHypercohomology

/-! # Ordinary Cech -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OrdinaryCech

noncomputable section

/-! The ordinary section-family Čech–de Rham total computes the preserved algebraic hypercohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {ι : Type} (U : ι → X.left.Opens)

def algebraicOrdinaryCechTotalInt : CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  Complex.SheafCechTotal.complexSheafOrdinaryCechTotalInt (TopCat.of X.left) U (Sheaves.algebraicDeRhamSheafComplex X)

def algebraicOrdinaryAdditiveCechTotalInt : CochainComplex AddCommGrpCat.{0} ℤ :=
  ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℤ)).obj
    (algebraicOrdinaryCechTotalInt X U)

def algebraicOrdinaryCechTotalIso :
    CechSectionsTotal.algebraicCechSectionsTotalInt X U ≅ algebraicOrdinaryAdditiveCechTotalInt X U :=
  Complex.SheafCechTotal.complexSheafCechTotalIso (TopCat.of X.left) U (Sheaves.algebraicDeRhamSheafComplex X)

variable [Smooth X.hom] [IsSeparated X.hom] [Finite ι]

def finiteAffine_algebraicOrdinaryCechHypercohomologyEquiv
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤) (n : ℕ) :
    (algebraicOrdinaryAdditiveCechTotalInt X U).homology (n : ℤ) ≃+ Sheaves.algebraicDeRham X n :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (n : ℤ)).mapIso
    (algebraicOrdinaryCechTotalIso X U).symm).addCommGroupIsoToAddEquiv.trans
      (CechSectionsHypercohomology.finiteAffine_algebraicCechSectionsHypercohomologyEquiv X U hU hcover n)

def smooth_algebraicHypercohomologyOrdinaryCechEquiv [QuasiCompact X.hom] (n : ℕ) :
    (algebraicOrdinaryAdditiveCechTotalInt X (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens X)).homology (n : ℤ) ≃+
      Sheaves.algebraicDeRham X n :=
  finiteAffine_algebraicOrdinaryCechHypercohomologyEquiv X (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens X)
    (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens_affine X) (Betti.Finite.AffineCover.finiteAlgebraicAffineOpens_cover X) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OrdinaryCech
