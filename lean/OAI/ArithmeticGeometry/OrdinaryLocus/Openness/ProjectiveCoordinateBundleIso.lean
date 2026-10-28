import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameGluing
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveTwistComparison

/-! # Projective Coordinate Bundle Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateBundleIso.Construction

noncomputable section

/-! Changing the coordinate used to model the hyperplane bundle preserves the actual line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveCoordinateBundle_iso (j k : σ) :
    Nonempty ((AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) k).sheaf) := by
  change Nonempty (AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j ≅
    AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) k)
  let U : ULift.{u} σ → (Proj (MvPolynomial.homogeneousSubmodule σ R)).Opens :=
    fun i => AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i.down
  let s := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j
  let t := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) k
  have hs (i : σ) : AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
    (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing j i).symm.le
  have ht (i : σ) : AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ≤ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i) :=
    (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing k i).symm.le
  refine SectionFrameGluing.Construction.lineBundleIso_of_section_coordinates U
    (fun x => ?_) (fun i => s i.down) (fun i => t i.down)
    (fun i => hs i.down) (fun i => ht i.down) ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i : σ, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i by
        rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]; trivial)
    exact ⟨⟨i⟩, hi⟩
  · intro i l V hi _ r
    rw [FrameCoordinatePullback.Construction.sectionAppCoordinate_smul, FrameCoordinatePullback.Construction.sectionAppCoordinate_smul]
    apply congrArg (fun a => r * a)
    have h₁ := FrameCoordinatePullback.Construction.sectionAppCoordinate_restrict (s i.down) (s l.down) hi (hs i.down)
    have h₂ := FrameCoordinatePullback.Construction.sectionAppCoordinate_restrict (t i.down) (t l.down) hi (ht i.down)
    have e₁ := ProjectiveCoordinateRatios.Construction.projective_sectionAppCoordinate (R := R) i.down j l.down
    have e₂ := ProjectiveCoordinateRatios.Construction.projective_sectionAppCoordinate (R := R) i.down k l.down
    rw [e₁] at h₁
    rw [e₂] at h₂
    exact h₁.symm.trans h₂

def projectiveCoordinateBundleIso (j k : σ) :
    (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) k).sheaf :=
  (projectiveCoordinateBundle_iso j k).some

def projectiveTwistCoordinateIso (j k : σ) (n : ℕ) :
    AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) k n :=
  ProjectiveTwistComparison.Construction.projectiveTwistTensorPowerIso j n ≪≫
    ProjectiveTwistComparison.Construction.sheafTensorPowerCongr (projectiveCoordinateBundleIso j k) n ≪≫
      (ProjectiveTwistComparison.Construction.projectiveTwistTensorPowerIso k n).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateBundleIso.Construction
