import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.ConeCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction

/-! # Specialization Locality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.SpecializationLocality.BundleCycles

noncomputable section

/-!
# LineBundleCycles: affine locality of global closed-support specialization

The divisor multiplicities on each support deformation chart agree with
their global values. The canonical normal-cone chart therefore recovers
the earlier affine specialization cycle, with the same coefficients.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)
variable [AlgebraicGeometry.IsNoetherian X]

instance supportCoefficientRing_noetherian (U : X.AffineZariskiSite) :
    IsNoetherianRing ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) :=
  inferInstanceAs (IsNoetherianRing (Γ(X, U.1) ⧸ P.ideal U))

variable [IsIntegral P.subscheme]

/-- The actual prime ideal of a nonempty integral support in an ambient affine chart. -/
def supportAffinePrime (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))] : PrimeSpectrum Γ(X, U.1) :=
  ⟨P.ideal U, (Ideal.Quotient.isDomain_iff_prime (P.ideal U)).mp (Integrality.BundleCycles.supportCoefficientRing_isDomain P U)⟩

/-- The global divisor of t restricts to the actual affine support divisor. -/
theorem globalSupportParameterDivisor_on_chart (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))]
    (x : (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U) :
    Specialization.BundleCycles.globalSupportParameterDivisor I P ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U x) =
      Affine.Specialization.BundleCycles.affineDeformationParameterDivisor (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) x := by
  have : IsIntegral ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U) :=
    inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))))
  have : AlgebraicGeometry.IsNoetherian ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).X U) :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian
      (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)))))
  have h := DivisorRestriction.BundleCycles.regularFunctionDivisor_openImmersion ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U)
    (Specialization.BundleCycles.globalSupportParameterSection I P) (Specialization.BundleCycles.globalSupportParameterSection_ne_zero I P) x
  rw [Specialization.BundleCycles.globalSupportParameterSection_on_chart I P U] at h
  exact h.symm

/-- The global support fiber cycle has exactly the earlier affine normal-cone coefficients. -/
theorem globalSupportFiberCycle_on_chart (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))]
    (x : Normal.Cone.BundleCycles.affineNormalCone (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)) :
    Specialization.BundleCycles.globalSupportFiberCycle I P (ConeCharts.BundleCycles.globalSupportNormalConeChartMap I P U x) =
      Affine.Specialization.BundleCycles.affineSpecializationCycle (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) x := by
  have h := congrArg (fun k => k x) (ConeCharts.BundleCycles.globalSupportNormalConeChartMap_fst I P U)
  change Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P (ConeCharts.BundleCycles.globalSupportNormalConeChartMap I P U x) =
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) x) at h
  change Specialization.BundleCycles.globalSupportParameterDivisor I P
      (Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P (ConeCharts.BundleCycles.globalSupportNormalConeChartMap I P U x)) = _
  rw [h]
  exact globalSupportParameterDivisor_on_chart I P U (Affine.Specialization.BundleCycles.normalConeFiberInclusion (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) x)

/-- The pushed global specialization keeps the affine support's exact multiplicity. -/
theorem globalClosedSupportSpecialization_on_chart (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))]
    (x : Normal.Cone.BundleCycles.affineNormalCone (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)) :
    Specialization.BundleCycles.globalClosedSupportSpecialization I P
        (Global.Specialization.BundleCycles.globalNormalConeChartMap I U (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U) x)) =
      Affine.Specialization.BundleCycles.affineSpecializationCycle (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) x := by
  have h := congrArg (fun k => k x) (ConeCharts.BundleCycles.globalSupportNormalConeChartMap_snd I P U)
  change Specialization.BundleCycles.globalSupportSpecialFiberMap I P (ConeCharts.BundleCycles.globalSupportNormalConeChartMap I P U x) =
    Global.Specialization.BundleCycles.globalNormalConeChartMap I U (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U) x) at h
  have hc : Specialization.BundleCycles.globalClosedSupportSpecialization I P
      (Specialization.BundleCycles.globalSupportSpecialFiberMap I P (ConeCharts.BundleCycles.globalSupportNormalConeChartMap I P U x)) =
      Specialization.BundleCycles.globalSupportFiberCycle I P (ConeCharts.BundleCycles.globalSupportNormalConeChartMap I P U x) :=
    Finsupp.embDomain_apply_self _ _ _
  exact (congrArg (Specialization.BundleCycles.globalClosedSupportSpecialization I P) h).symm.trans
    (hc.trans (globalSupportFiberCycle_on_chart I P U x))

/-- Every affine coefficient, including those outside the support cone, agrees with the affine construction. -/
theorem globalClosedSupportSpecialization_affine_coeff (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))]
    (x : Normal.Cone.BundleCycles.affineNormalCone (I.ideal U)) :
    Specialization.BundleCycles.globalClosedSupportSpecialization I P (Global.Specialization.BundleCycles.globalNormalConeChartMap I U x) =
      CycleSpecialization.BundleCycles.affinePrimeSpecialization (I.ideal U) (supportAffinePrime P U) x := by
  classical
  by_cases hx : x ∈ Set.range (CycleSpecialization.BundleCycles.closedSupportNormalConeInclusion (I.ideal U) (P.ideal U))
  · obtain ⟨y, rfl⟩ := hx
    exact (globalClosedSupportSpecialization_on_chart I P U y).trans
      (CycleSpecialization.BundleCycles.affinePrimeSpecialization_at_support (I.ideal U) (supportAffinePrime P U) y).symm
  · have hglobal : Global.Specialization.BundleCycles.globalNormalConeChartMap I U x ∉ Set.range (Specialization.BundleCycles.globalSupportSpecialFiberMap I P) := by
      rintro ⟨y, hy⟩
      obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
        (ConeCharts.BundleCycles.globalSupportNormalConeChart_ambient_isPullback I P U) x y hy.symm
      exact hx ⟨z, hz⟩
    have hG : Specialization.BundleCycles.globalClosedSupportSpecialization I P (Global.Specialization.BundleCycles.globalNormalConeChartMap I U x) = 0 :=
      Finsupp.embDomain_of_notMem_range _ _ _ hglobal
    have hA : CycleSpecialization.BundleCycles.affinePrimeSpecialization (I.ideal U) (supportAffinePrime P U) x = 0 :=
      Finsupp.embDomain_of_notMem_range _ _ _ hx
    exact hG.trans hA.symm

/-- Restricting the global finite cycle gives exactly the earlier affine prime specialization. -/
theorem globalClosedSupportSpecialization_affine_restrict (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))] :
    Finsupp.comapDomain (Global.Specialization.BundleCycles.globalNormalConeChartMap I U) (Specialization.BundleCycles.globalClosedSupportSpecialization I P)
        (Global.Specialization.BundleCycles.globalNormalConeChartMap I U).isOpenEmbedding.injective.injOn =
      CycleSpecialization.BundleCycles.affinePrimeSpecialization (I.ideal U) (supportAffinePrime P U) := by
  ext x
  exact globalClosedSupportSpecialization_affine_coeff I P U x

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.SpecializationLocality.BundleCycles
