import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Terms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso

/-! # Sections Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionsTotal.IntrinsicCechSectionsTotal

noncomputable section

/-! The actual native Čech section complex is the finite-diagonal total of its ordinary section bicomplex. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Scheme.{0}) {ι : Type} (U : ι → X.Opens)
  (K : CochainComplex (Bicomplex.IntrinsicCechBicomplex.Sheaves R X) ℕ)

local instance : HasCoproducts.{0} (Bicomplex.IntrinsicCechBicomplex.Sheaves R X) :=
  Instances.IntrinsicCechInstances.hasCoproducts R X
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X)).Additive where
  map_add := rfl

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X))
    (Bicomplex.IntrinsicCechBicomplex.bicomplex R X U K)

def integerTotal : CochainComplex (ModuleCat.{0} R) ℤ :=
  ((bicomplex R X U K).total (.up ℕ)).extend ComplexShape.embeddingUpNat

def iso : integerTotal R X U K ≅ Terms.IntrinsicCechComparison.sections R X U K :=
  Finite.TotalIso.FiniteTotalExtension.iso (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X))
    (Bicomplex.IntrinsicCechBicomplex.bicomplex R X U K)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionsTotal.IntrinsicCechSectionsTotal
