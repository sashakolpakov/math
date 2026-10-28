import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelZero
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter

/-! # Subspace Chart Model -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Retained coordinate charts supply actual smooth integral affine models and exact common marked inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {x : X}

abbrev Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelScheme (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : Scheme :=
  Spec (.of (MvPolynomial (C.normal ⊕ Fin C.freeDimension) ℂ))

abbrev Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelStructure (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : C.modelScheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (C.normal ⊕ Fin C.freeDimension) ℂ)

abbrev Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelIdeal (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : C.modelScheme.IdealSheafData :=
  Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom)

def Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelMap (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : Spec C.ring ⟶ C.modelScheme :=
  Spec.map (CommRingCat.ofHom C.coordinate.toRingHom)

instance Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelStructure_smooth (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : Smooth C.modelStructure := by
  let : Algebra.Smooth ℂ (MvPolynomial (C.normal ⊕ Fin C.freeDimension) ℂ) := ⟨inferInstance, inferInstance⟩
  infer_instance

instance Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelMap_etale (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : Etale C.modelMap :=
  (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom C.coordinate.toRingHom)).mpr C.coordinate_etale

theorem Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelMap_ground (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) :
    C.modelMap ≫ C.modelStructure = C.map ≫ f := by
  rw [C.ground]
  change Spec.map (CommRingCat.ofHom C.coordinate.toRingHom) ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure _ = _
  rw [ComplexAffineDifferentialIdeal.Construction.complexSpecStructure, ← Spec.map_comp]
  apply congrArg Spec.map
  have he : C.coordinate.toRingHom.comp (algebraMap ℂ (MvPolynomial (C.normal ⊕ Fin C.freeDimension) ℂ)) =
      algebraMap ℂ C.ring := by
    apply RingHom.ext
    intro c
    exact C.coordinate.commutes c
  exact congrArg CommRingCat.ofHom he

theorem Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelMap_ideal (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) :
    C.modelIdeal.comap C.modelMap = J.comap C.map := by
  rw [Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelIdeal, Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelMap, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom]
  exact C.ideal_eq.symm

theorem Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.modelIdeal_ne_bot (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : C.modelIdeal ≠ ⊥ := by
  intro hz
  apply C.modelNonzero
  apply le_bot_iff.mp
  apply (Affine.IdealChartDescent.Construction.affineQuotientKernel_le_iff _ _).mp
  rw [Affine.KernelZero.Construction.affineQuotientKernel_bot]
  exact hz.le

theorem Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.chartIdeal_ne_bot (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) : J.comap C.map ≠ ⊥ := by
  rw [← C.modelMap_ideal]
  exact Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_nonempty_etale_ne_bot C.modelMap C.modelIdeal C.modelIdeal_ne_bot

end

end OAI.AlgebraicGeometry.Resolution.Blowups
