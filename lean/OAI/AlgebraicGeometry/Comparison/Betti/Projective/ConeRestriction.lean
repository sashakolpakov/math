import OAI.AlgebraicGeometry.Comparison.Betti.Projective.AnalyticConeCoordinates
import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousSectorSingle

/-! # Cone Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConeRestriction.Dolbeault

noncomputable section

/-! Original twist restrictions become homogeneous function restriction and sector inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAnalyticConePoint_ratio (n : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) (i k : Fin (n + 1)) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i k ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n s hs x).val) =
      x.val k / x.val i := ProjectiveTwist.Cone.Dolbeault.projectiveConePoint_ratio n s hs x i k

theorem projectiveTwistAnalyticConeCoordinates_restrict (n : ℕ)
    {s t : Finset (Fin (n + 1))} (hst : s ⊆ t)
    (i : Fin (n + 1)) (hi : i ∈ t) (k : Fin (n + 1)) (hk : k ∈ s)
    (j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)))) :
    AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n t i hi j d
        ((ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map (homOfLE (Open.SmoothForms.analyticOpen_mono
          (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n hst))).op a) =
      HomogeneousSectorSingle.Dolbeault.laurentHomogeneousSectionRestrict hst d (AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n s k hk j d a) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let b : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n t))) :=
    (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map (homOfLE (Open.SmoothForms.analyticOpen_mono
      (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n hst))).op a
  let xs : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s := ⟨x.val, Laurent.SectorTo.Dolbeault.laurentCoordinateDomain_antitone hst x.property⟩
  let p := AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n t ⟨i, hi⟩ x
  let z : ℂ := ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n s k hk j d a
    (AnalyticConeCoordinates.Dolbeault.projectiveAnalyticConePoint n s ⟨k, hk⟩ xs)
  have hval : ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n t i hi j d b p = z * (x.val k / x.val i) ^ d :=
    (ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction_restrict n hst i hi k hk j d a p).trans
      (congrArg (fun c : ℂ => z * c ^ d) (projectiveAnalyticConePoint_ratio n t ⟨i, hi⟩ x i k))
  have hcancel : x.val i ^ d * (z * (x.val k / x.val i) ^ d) = x.val k ^ d * z := by
    rw [div_zpow, div_eq_mul_inv]
    have hxi : x.val i ^ d ≠ 0 :=
      zpow_ne_zero d ((Laurent.SectorTo.Dolbeault.mem_laurentCoordinateDomain t x.val).mp x.property i hi)
    calc
      x.val i ^ d * (z * (x.val k ^ d * (x.val i ^ d)⁻¹)) =
          (x.val i ^ d * (x.val i ^ d)⁻¹) * (x.val k ^ d * z) := by ring
      _ = x.val k ^ d * z := by rw [mul_inv_cancel₀ hxi, one_mul]
  exact (AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates_evaluate n t ⟨i, hi⟩ i hi j d b x).trans
    ((congrArg (x.val i ^ d * ·) hval).trans (hcancel.trans
      (AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates_evaluate n s ⟨k, hk⟩ k hk j d a xs).symm))

def projectiveTwistAnalyticSectorCoordinates (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s))) ≃+
        HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d :=
  (AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n s i hi j d).trans (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d).toAddEquiv

theorem projectiveTwistAnalyticSectorCoordinates_restrict (n : ℕ)
    {s t : Finset (Fin (n + 1))} (hst : s ⊆ t)
    (i : Fin (n + 1)) (hi : i ∈ t) (k : Fin (n + 1)) (hk : k ∈ s)
    (j : Fin (n + 1)) (d : ℤ)
    (a : (ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj
      (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Intersections.Dolbeault.projectiveAlgebraicIntersection n s)))) :
    projectiveTwistAnalyticSectorCoordinates n t i hi j d
        ((ProjectiveTwist.Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.map (homOfLE (Open.SmoothForms.analyticOpen_mono
          (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n hst))).op a) =
      HomogeneousSectorSingle.Dolbeault.laurentHomogeneousFamilyInclusion hst d (projectiveTwistAnalyticSectorCoordinates n s k hk j d a) := by
  exact (congrArg (fun f : HomogeneousLaurent.Dolbeault.laurentHomogeneousSections t d => HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv t d f)
    (projectiveTwistAnalyticConeCoordinates_restrict n hst i hi k hk j d a)).trans
      (HomogeneousSectorSingle.Dolbeault.homogeneousLaurentSectorEquiv_restrict hst d (AnalyticConeCoordinates.Dolbeault.projectiveTwistAnalyticConeCoordinates n s k hk j d a))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConeRestriction.Dolbeault
