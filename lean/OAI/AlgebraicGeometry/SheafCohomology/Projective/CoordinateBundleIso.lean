import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameGluing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers

/-! # Coordinate Bundle Iso -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateBundleIso.Dimension

noncomputable section

/-! Changing the coordinate used to model the hyperplane bundle preserves the actual line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveCoordinateBundle_iso (j k : σ) :
    Nonempty ((Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) k).sheaf) := by
  change Nonempty (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j ≅
    HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) k)
  let U : ULift.{u} σ → (Proj (MvPolynomial.homogeneousSubmodule σ R)).Opens :=
    fun i => MvPolynomialClosure.MvPolynomial.coordinateOpen i.down
  let s := Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j
  let t := Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) k
  have hs (i : σ) : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
    (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing j i).symm.le
  have ht (i : σ) : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i) :=
    (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing k i).symm.le
  refine ArithmeticGeometry.OrdinaryLocus.Openness.SectionFrameGluing.Construction.lineBundleIso_of_section_coordinates U
    (fun x => ?_) (fun i => s i.down) (fun i => t i.down)
    (fun i => hs i.down) (fun i => ht i.down) ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i : σ, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i by
        rw [MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]; trivial)
    exact ⟨⟨i⟩, hi⟩
  · intro i l V hi _ r
    rw [ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate_smul, ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate_smul]
    apply congrArg (fun a => r * a)
    have h₁ := ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate_restrict (s i.down) (s l.down) hi (hs i.down)
    have h₂ := ArithmeticGeometry.OrdinaryLocus.Openness.FrameCoordinatePullback.Construction.sectionAppCoordinate_restrict (t i.down) (t l.down) hi (ht i.down)
    have e₁ := ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios.Construction.projective_sectionAppCoordinate (R := R) i.down j l.down
    have e₂ := ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios.Construction.projective_sectionAppCoordinate (R := R) i.down k l.down
    rw [e₁] at h₁
    rw [e₂] at h₂
    exact h₁.symm.trans h₂

def projectiveCoordinateBundleIso (j k : σ) :
    (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) k).sheaf :=
  (projectiveCoordinateBundle_iso j k).some

def projectiveTwistCoordinateIso (j k : σ) (n : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) k n :=
  UniversalPowers.Dimension.projectiveTwistUniversalPowerIso j n ≪≫
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor _ n).mapIso (projectiveCoordinateBundleIso j k) ≪≫
      (UniversalPowers.Dimension.projectiveTwistUniversalPowerIso k n).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateBundleIso.Dimension
