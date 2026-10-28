import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechFactors
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ConeUnit

/-! # Cech Cone Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechConeEvaluation.Dolbeault

noncomputable section

/-! Evaluate the original projective Čech comparison on homogeneous cone points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveTwistCechConeValue (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q)
    (t : Fin (q + 1) → Fin (n + 1)) (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t)) : ℂ :=
  (Projective.AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n (Finset.univ.image t) (t 0)
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d
    ((Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d q t).hom
      (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj (Projective.Intersections.Dolbeault.projectiveStandardCover n) q z t))).val.val x

def projectiveAlgebraicTwistCechFrameCoefficient (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1)) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)) :=
  ConeUnit.Dolbeault.projectiveAlgebraicTwistIntersectionCoefficient n (Finset.univ.image t) (t 0)
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d
    ((ReferenceCechMap.Dolbeault.projectiveAlgebraicCechSectionIso n j d q t).hom
      (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf
        (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) q z t))

theorem projectiveTwistCechConeValue_original_map (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : (ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d).X q) (t : Fin (q + 1) → Fin (n + 1))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain (Finset.univ.image t)) :
    projectiveTwistCechConeValue n j d q ((ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d).f q z) t x =
      x.val (t 0) ^ d * Holomorphic.RegularSections.regularHolomorphicSectionMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t))
        (projectiveAlgebraicTwistCechFrameCoefficient n j d q z t)
          (Projective.AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n (Finset.univ.image t)
            (Finset.image_nonempty.mpr (Finset.univ_nonempty)) x) := by
  have h := ReferenceCechFactors.Dolbeault.projectiveTwistOriginalCechMap_factor_apply n j d q t z
  have he := congrArg (fun a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)))) =>
    (Projective.AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n (Finset.univ.image t) (t 0)
      (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d a).val.val x) h
  exact he.trans (ConeUnit.Dolbeault.projectiveTwistAnalyticConeCoordinates_unit n (Finset.univ.image t)
    (Finset.image_nonempty.mpr Finset.univ_nonempty) (t 0)
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d _ x)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechConeEvaluation.Dolbeault
