import OAI.RepresentationTheory.Theta.Geometric.SchemeTangents
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold

/-! # Tangent Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts

noncomputable section

/-! The preferred native manifold chart gives actual dual-number tangent
points, with the literal scalar operation on the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold ChartedSpace

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- Affine witnesses for the already chosen native manifold chart. -/
structure NativeTangentChart (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) where
  U : X.left.Opens
  affine : IsAffineOpen U
  chart : OpenPartialHomeomorph
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) ModelX
  regular : chart ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
  chart_eq : chartAt ModelX p =
    AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U affine) chart
  point : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
  source : point ∈ chart.source
  point_eq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U affine point = p

theorem nativeTangentChart_nonempty (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Nonempty (NativeTangentChart X p) := by
  obtain ⟨U, hU, e, he, hc⟩ := chart_mem_atlas ModelX p
  have hp := mem_chart_source ModelX p
  rw [hc] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  exact ⟨⟨U, hU, e, he, hc, x, hx, hxp⟩⟩

def nativeTangentChart (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : NativeTangentChart X p :=
  (nativeTangentChart_nonempty X p).some

namespace NativeTangentChart

variable {X} {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X} (C : NativeTangentChart X p)

abbrev algebra := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X C.U

instance : Algebra C.algebra ℂ := C.point.toRingHom.toAlgebra
instance : IsScalarTower ℂ C.algebra ℂ := IsScalarTower.of_algHom C.point
instance : Algebra.Smooth ℂ C.algebra :=
  AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X C.U C.affine

theorem basePoint_eq :
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ Affine.Tangents.affineTangentBasePoint ℂ C.algebra) ≫
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine = p := by
  have h : IsScalarTower.toAlgHom ℂ C.algebra ℂ = C.point := AlgHom.ext (fun _ => rfl)
  change (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C.algebra ℂ
    (IsScalarTower.toAlgHom ℂ C.algebra ℂ)) ≫ _ = _
  rw [h]
  exact C.point_eq

def tangentEquiv : ModelX ≃ SchemeTangents.schemeTangentPoints X p :=
  (SchemeTangents.regularNeighborhoodTangentEquiv X
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine)
    C.chart C.regular C.point C.source (fun _ => rfl)).trans
      (Equiv.subtypeEquivRight (fun _ => by rw [C.basePoint_eq]))

theorem tangentEquiv_apply (v : ModelX) :
    (C.tangentEquiv v).val =
      (SchemeTangents.complexDualNumberIso.inv ≫
        (Affine.Tangents.derivationAffineTangentEquiv ℂ C.algebra
          (RegularTangent.regularChartDerivation C.chart C.regular C.point C.source (fun _ => rfl) v)).val) ≫
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine := rfl

theorem tangentEquiv_smul (c : ℂ) (v : ModelX) :
    (C.tangentEquiv (c • v)).val =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar ℂ c ≫ (C.tangentEquiv v).val := by
  rw [C.tangentEquiv_apply, C.tangentEquiv_apply]
  exact SchemeTangents.regularNeighborhoodTangent_smul X
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine)
    C.chart C.regular C.point C.source (fun _ => rfl) c v

end NativeTangentChart

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts
