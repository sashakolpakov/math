import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.CechHypercohomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionTotal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperDeRhamCechFiniteness
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Base Cech Hypercohomology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.BaseCechHypercohomology.FlatBaseCechHypercohomology

noncomputable section

/-! # Original de Rham hypercohomology is the cohomology of the actual direct affine Čech total -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type u} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

def integerEquiv (n : ℕ) :
    (Cech.SectionTotal.CechSectionTotal.directTotal R X U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).homology (n : ℤ) ≃ₗ[R]
      DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  (HomologicalComplex.homologyMapIso (Cech.SectionTotal.CechSectionTotal.iso R X U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))
    (n : ℤ)).toLinearEquiv.trans (CechHypercohomology.FlatBaseCechHypercohomology.equiv R X U hU hcover n)

def equiv (n : ℕ) :
    ((Cech.SectionTotal.CechSectionTotal.directBicomplex R X U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).total (.up ℕ)).homology n ≃ₗ[R]
      DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  (((Cech.SectionTotal.CechSectionTotal.directBicomplex R X U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).total (.up ℕ)).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) rfl).symm.toLinearEquiv.trans
      (integerEquiv R X U hU hcover n)

def properEquiv (n : ℕ) : (Base.ProperDeRhamCechFiniteness.BaseSmoothProperDeRhamCechFiniteness.total R X).homology n ≃ₗ[R]
    DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  equiv R X (Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens R X)
    (Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.affine R X) (Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.cover R X) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.BaseCechHypercohomology.FlatBaseCechHypercohomology
