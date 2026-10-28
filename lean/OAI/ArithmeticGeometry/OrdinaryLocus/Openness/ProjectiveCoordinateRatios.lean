import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp

/-! # Projective Coordinate Ratios -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios.Construction

noncomputable section

/-! The ratios of the projective coordinate sections are the usual affine coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem sectionAppCoordinate_of_overFrame {X : Scheme.{u}} {M : X.Modules}
    (s t : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (U : X.Opens) (hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (r : Γ(X, U))
    (hs : e.hom.val.app (.op (Over.mk (𝟙 U))) (s.app U (1 : Γ(X, U))) = (1 : Γ(X, U)))
    (ht : e.hom.val.app (.op (Over.mk (𝟙 U))) (t.app U (1 : Γ(X, U))) = r) :
    FrameCoordinatePullback.Construction.sectionAppCoordinate s t hU = r := by
  apply (SectionFrameApps.Construction.sectionAppLinearEquiv s hU).injective
  let eU := (SheafOfModules.evaluation (X.ringCatSheaf.over U) (.op (Over.mk (𝟙 U)))).mapIso e
  apply eU.toLinearEquiv.injective
  have h₁ : s.app U (FrameCoordinatePullback.Construction.sectionAppCoordinate s t hU) = t.app U (1 : Γ(X, U)) :=
    (SectionFrameApps.Construction.sectionAppLinearEquiv s hU).apply_symm_apply _
  have h₂ : s.app U r = r • s.app U (1 : Γ(X, U)) := by
    have hh := s.app_smul r (1 : Γ(X, U))
    change s.app U (show Γ(X, U) from r * 1) = r • s.app U (1 : Γ(X, U)) at hh
    exact (congrArg (fun z : Γ(X, U) => s.app U z) (mul_one r)).symm.trans hh
  change e.hom.val.app (.op (Over.mk (𝟙 U))) (s.app U (FrameCoordinatePullback.Construction.sectionAppCoordinate s t hU)) =
    e.hom.val.app (.op (Over.mk (𝟙 U))) (s.app U r)
  rw [h₁, h₂, ht]
  exact ((e.hom.val.app (.op (Over.mk (𝟙 U)))).hom.map_smul r _).trans
    ((congrArg (fun z : Γ(X, U) => r * z) hs).trans (mul_one r)) |>.symm

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_sectionAppCoordinate (i j k : σ) :
    FrameCoordinatePullback.Construction.sectionAppCoordinate (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i)
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k)
      (le_of_eq (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := R) j i).symm) =
        AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k := by
  apply sectionAppCoordinate_of_overFrame _ _ _ _ (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.frame i j)
  · rw [AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_app]
    exact (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationSection_coefficient _ _ _ _).trans
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self (R := R) i)
  · rw [AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_app]
    exact AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationSection_coefficient _ _ _ _

theorem projective_local_frameCoordinate (i j k : σ) :
    let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
    let s := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i
    let t := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k
    letI := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le
      (le_of_eq (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := R) j i).symm) s
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι t) =
      U.topIso.inv (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) := by
  let U := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
  let s := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i
  let t := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k
  have hU : U ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := R) j i).symm.le
  have : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PowerLocus.pullbackSection_isIso_of_le hU s
  apply (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective
  exact (FrameCoordinatePullback.Construction.sectionAppCoordinate_eq_frameCoordinate s t hU).symm.trans
    ((projective_sectionAppCoordinate i j k).trans
      (ConcreteCategory.congr_hom U.topIso.inv_hom_id _).symm)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios.Construction
