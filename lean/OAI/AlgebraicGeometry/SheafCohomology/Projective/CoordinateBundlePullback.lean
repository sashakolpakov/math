import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateFraction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionCoordinatePullback
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRatioGluing
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase

/-! # Coordinate Bundle Pullback -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateBundlePullback

noncomputable section

/-! A graded map preserving the homogeneous coordinate variables pulls the
actual hyperplane bundle back to the hyperplane bundle over the new ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type} [CommRing R] [CommRing S] (n : ℕ)
  (g : homogeneousSubmodule (Fin (n + 1)) R →+*ᵍ homogeneousSubmodule (Fin (n + 1)) S)
  (hg : HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (n + 1)) S) ≤
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (n + 1)) R)).map g)
  (hX : ∀ i : Fin (n + 1), g (X i) = X i)

include hX

theorem coordinatePreservingMap_preimage (i : Fin (n + 1)) :
    Proj.map g hg ⁻¹ᵁ MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i = MvPolynomialClosure.MvPolynomial.coordinateOpen (R := S) i := by
  change Proj.map g hg ⁻¹ᵁ Proj.basicOpen _ (X i) = _
  rw [Proj.map_preimage_basicOpen, hX]

theorem coordinatePreservingMap_appLE (i k : Fin (n + 1)) :
    (Proj.map g hg).appLE (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := S) i)
      (coordinatePreservingMap_preimage n g hg hX i).symm.le
      (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) =
        CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := S) i k := by
  rw [HyperplaneCoordinateFraction.coordinateHyperplaneLocalEquation_eq_fraction, HyperplaneCoordinateFraction.coordinateHyperplaneLocalEquation_eq_fraction]
  exact HyperplaneCoordinateFraction.projectiveCoordinateSection_appLE_of_eq g hg (X i) (X k)
    (isHomogeneous_X R i) (isHomogeneous_X R k) (X i) (X k)
    (isHomogeneous_X S i) (isHomogeneous_X S k) (hX i) (hX k)

theorem coordinatePreservingMap_bundle_iso (j l : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback (Proj.map g hg)).obj
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
        (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := S) l).sheaf) := by
  let f := Proj.map g hg
  let U : Fin (n + 1) → (Proj (homogeneousSubmodule (Fin (n + 1)) S)).Opens :=
    fun i => MvPolynomialClosure.MvPolynomial.coordinateOpen (R := S) i
  let s := Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := S) l
  let t (i : Fin (n + 1)) := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i)
  have hs (i : Fin (n + 1)) : U i ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) :=
    (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := S) l i).symm.le
  have ht (i : Fin (n + 1)) : U i ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (t i) := by
    have h := Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j)
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i)
    rw [Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing,
      coordinatePreservingMap_preimage n g hg hX] at h
    exact h.symm.le
  refine ArithmeticGeometry.OrdinaryLocus.Openness.SectionRatioGluing.Construction.lineBundleIso_of_sectionAppCoordinates U ?_ t s ht hs ?_
  · intro x
    apply Opens.mem_iSup.mp
    change x ∈ ⨆ i : Fin (n + 1), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := S) i
    rw [MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  · intro i k
    have h := SectionCoordinatePullback.sectionAppCoordinate_pullbackLE f
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j i)
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom (R := R) j k)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (U i)
      (coordinatePreservingMap_preimage n g hg hX i).symm.le
      (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.sectionHom_nonvanishing (R := R) j i).symm.le (ht i)
    rw [ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios.Construction.projective_sectionAppCoordinate, coordinatePreservingMap_appLE n g hg hX] at h
    exact h.trans (ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCoordinateRatios.Construction.projective_sectionAppCoordinate (R := S) i l k).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateBundlePullback
