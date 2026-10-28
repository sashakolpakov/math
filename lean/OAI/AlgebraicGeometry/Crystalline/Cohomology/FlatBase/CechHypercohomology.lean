import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.CechTotalAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionHypercohomologyInv
import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiHom

/-! # Cech Hypercohomology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.CechHypercohomology.FlatBaseCechHypercohomology

noncomputable section

/-! # The finite affine Čech total computes original smooth proper de Rham hypercohomology -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type u} [Finite ι] (U : ι → X.left.Opens)

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

def sectionComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  SectionHypercohomologyInv.SectionHypercohomology.sectionComplex R (TopCat.of X.left)
    (MixedCech.ComplexResolution.MixedCechComplexResolution.integerTotal R X.left U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))

def equiv (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤) (n : ℕ) :
    (sectionComplex R X U).homology (n : ℤ) ≃ₗ[R] DeRhamGlobalId.DeRhamGlobal.cohomology R X n := by
  let K := DeRhamGlobalId.DeRhamGlobal.sheafComplex R X
  let L := MixedCech.ComplexResolution.MixedCechComplexResolution.integerTotal R X.left U K
  have : L.IsStrictlyGE 0 := MixedCech.ComplexResolution.MixedCechComplexResolution.integerTotal_nonnegative R X.left U K
  let a := MixedCech.ComplexResolution.MixedCechComplexResolution.integerEdge R X.left U K
  have : QuasiIso a := MixedCech.ComplexResolution.MixedCechComplexResolution.integerEdge_quasiIso R X.left U K hcover
  let e₁ := SectionHypercohomologyInv.SectionHypercohomology.equiv R (TopCat.of X.left) L 0
    (CechTotalAcyclic.FlatBaseCechTotalAcyclic.integerTotal R X U hU) (n : ℤ)
  let e₂ := NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiHom.DerivedQuasiIsoHom.equiv R (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) a (n : ℤ)
  exact e₁.trans e₂

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.CechHypercohomology.FlatBaseCechHypercohomology
