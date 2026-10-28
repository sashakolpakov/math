import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureAntilinearCovector
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars

/-! # Scheme Structure Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.SchemeStructureBound

noncomputable section

/-! The H1 bound holds on the original projectively presented abelian
scheme, with its actual complex scalar action and relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)

include P

theorem abelianSchemeStructureH1_finiteDimensional :
    let := StructureComplexScalars.structureH1ComplexModule A.scheme
    FiniteDimensional ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) :=
  StructureAntilinearCovector.abelianStructureH1_finiteDimensional (IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)

theorem abelianSchemeStructureH1_finrank_le :
    let := StructureComplexScalars.structureH1ComplexModule A.scheme
    Module.finrank ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) ≤ g := by
  let := StructureComplexScalars.structureH1ComplexModule A.scheme
  exact (StructureAntilinearCovector.abelianStructureH1_finrank_le (IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).trans_eq
    (IntrinsicAdapter.AbelianIntrinsicAdapter.dimension_eq A)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.SchemeStructureBound
