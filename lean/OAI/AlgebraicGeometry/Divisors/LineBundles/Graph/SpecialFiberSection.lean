import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.IntegralDeformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiberCartier
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalImmersionPair

/-! # Special Fiber Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecialFiberSection.BundleCycles

noncomputable section

/-! The graph deformation's actual zero fiber has codimension one and its defining section has the principal kernels required by the native Thom comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphSpecialFiber_sectionZeroImage :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f)) =
      Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (DeformationTopology.BundleCycles.graphDeformationOver f) (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker)) := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f)).trans
  apply Eq.trans ?_ (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range (DeformationTopology.BundleCycles.graphDeformationOver f) (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker)).symm
  ext x
  have hr := congrArg (fun A : Set (Global.Deformation.BundleCycles.globalDeformation (OpenAmbient.BundleCycles.graph f).ker) => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ A)
    (Global.Specialization.BundleCycles.globalSpecialFiberMap_range (OpenAmbient.BundleCycles.graph f).ker)
  exact hr.to_iff.trans ((not_congr
    (CycleClass.Thom.GlobalSectionBasicOpen.Constructions.underlying_mem_basicOpen_iff (DeformationTopology.BundleCycles.graphDeformationOver f) (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker) x)).trans not_not)

theorem graphSpecialFiber_principal_affineNeighborhoods (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Conormal.BundleCycles.graphConeOver f)) :
    ∃ (U : (DeformationTopology.BundleCycles.graphDeformationOver f).left.Opens), IsAffineOpen U ∧
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f) x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen (DeformationTopology.BundleCycles.graphDeformationOver f) U ∧
      RingHom.ker ((CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f).left.app U).hom =
        Ideal.span {(DeformationTopology.BundleCycles.graphDeformationOver f).left.presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op (Global.Specialization.BundleCycles.globalDeformationParameterSection (OpenAmbient.BundleCycles.graph f).ker)} :=
  Global.SpecialFiberPrincipalKernel.BundleCycles.globalSpecialFiber_exists_principal_affineNeighborhood (OpenAmbient.BundleCycles.graph f).ker
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f) x))

variable [IsIntegral X.carrier] [IsIntegral Y.carrier]

theorem graphSpecialFiber_nativeCodimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Conormal.BundleCycles.graphConeOver f).hom + 1 =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (DeformationTopology.BundleCycles.graphDeformationOver f).hom :=
  Principal.ImmersionCodimension.BundleCycles.integralPrincipalImmersion_nativeCodimension (CenterEndpointFibers.BundleCycles.graphSpecialFiberOver f)
    (Global.SpecialFiberCartier.BundleCycles.globalSpecialFiber_regularPrincipalImageIdeals (OpenAmbient.BundleCycles.graph f).ker)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.SpecialFiberSection.BundleCycles
