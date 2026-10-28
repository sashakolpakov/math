import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCoordinatePeriodModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PrimitiveDifferenceComplexSurjectivity

/-! # Ample Complex Difference Surjectivity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.AmpleComplexDifferenceSurjectivity.Geometric

noncomputable section

/-! Every actual ample line on a complex abelian variety represents
every original homogeneous Picard class by translation. Its period
matrix and period model are constructed from that same ample line. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (hL : L.IsAmple)

theorem nativeIntegralChernMatrix_marks {g : ℕ} (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A) :
    IntrinsicPolarization.Geometric.PreservesPolarizationMatrix A L hL b (AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b) := by
  intro i j
  have h := AbelianModuli.ReferenceFamily.Intrinsic.RiemannForm.nativeRiemannForm_period A L hL
    (AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b i))
    (AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b j))
  exact h.trans (by exact_mod_cast (AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix_cast A L b i j).symm)

include hL in
theorem ampleDifference_complex_surjective
    (q : (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardSheaf.obj.obj (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) :
    ∃ a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) L) a =
        (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardSheafInclusion.hom.app
          (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) q := by
  let : IsIntegral A.toOver.left := A.variety.property
  let g := Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom
  let b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (DefinitionsIntegral.Index g) A := by
    change Module.Basis (Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom))
      ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    exact AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.periodBasis A
  let E : DefinitionsIntegral.IntegralMatrix g := AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix A L b
  have hE : E.transpose = -E := AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods.nativeIntegralChernMatrix_alternating A L b
  have hb : IntrinsicPolarization.Geometric.PreservesPolarizationMatrix A L hL b E := nativeIntegralChernMatrix_marks A L hL b
  obtain ⟨T, e, _, he, hH⟩ := IntrinsicPolarization.Geometric.native_polarized_comparison A L hL b E hb
  let M := IntrinsicCoordinatePeriodModel.Geometric.nativeCoordinatePeriodModel A L hL T e he
  exact M.primitiveDifference_complex_surjective hE L
    (IntrinsicCoordinatePeriodModel.Geometric.nativeCoordinatePeriodModel_chern A L hL T e he hH) q

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.AmpleComplexDifferenceSurjectivity.Geometric
