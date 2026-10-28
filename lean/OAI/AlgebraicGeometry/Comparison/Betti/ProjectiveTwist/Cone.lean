import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ConeOn
import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurent
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DomainCongr
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SectionCoordinates

/-! # Cone -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Cone.Dolbeault

noncomputable section

section

/-! Actual projective twist sections are normalized homogeneous Laurent sectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped BigOperators

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DomainCongr

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveIntersectionProduct_eq_laurentAffineDomain
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (i : ι) :
    ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (Projective.IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i) = Laurent.ConeCoordinates.Dolbeault.laurentAffineDomain s i := by
  ext z
  change (z ∈ ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (Projective.IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i)) ↔
    (z ∈ Laurent.ConeCoordinates.Dolbeault.laurentAffineDomain s i)
  rw [Projective.IntersectionDomains.Dolbeault.mem_projectiveIntersectionProduct, Laurent.ConeCoordinates.Dolbeault.mem_laurentAffineDomain]

def projectiveTwistConeCoordinates (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) ≃+
      HomogeneousLaurent.Dolbeault.laurentHomogeneousSections s d :=
  (SectionCoordinates.Dolbeault.projectiveTwistSectionCoordinates n s i hi j d).trans
    ((Holomorphic.DomainCongr.holomorphicFunctionDomainCongr (projectiveIntersectionProduct_eq_laurentAffineDomain s i)).toAddEquiv.trans
      (Laurent.ConeOn.Dolbeault.laurentConeSectionEquiv s i hi d).toAddEquiv)

def projectiveTwistSectorCoordinates (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) ≃+
      HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies s d :=
  (projectiveTwistConeCoordinates n s i hi j d).trans (HomogeneousLaurent.Dolbeault.homogeneousLaurentSectorEquiv s d).toAddEquiv

theorem projectiveTwistConeCoordinates_apply (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (projectiveTwistConeCoordinates n s i hi j d a).val.val x =
      x.val i ^ d * (SectionCoordinates.Dolbeault.projectiveTwistSectionCoordinates n s i hi j d a).val
        ⟨Laurent.ConeCoordinates.Dolbeault.laurentConeRatios i x.val,
          (projectiveIntersectionProduct_eq_laurentAffineDomain s i).ge
            (Laurent.ConeCoordinates.Dolbeault.laurentConeNormalize s i hi x).property⟩ := by
  change (Laurent.ConeOn.Dolbeault.laurentConeLiftSection s i hi d
    (Holomorphic.DomainCongr.holomorphicFunctionDomainCongr (projectiveIntersectionProduct_eq_laurentAffineDomain s i)
      (SectionCoordinates.Dolbeault.projectiveTwistSectionCoordinates n s i hi j d a))).val x = _
  rw [Laurent.ConeOn.Dolbeault.laurentConeLiftSection_apply, Holomorphic.DomainCongr.holomorphicFunctionDomainCongr_apply]
  rfl

theorem projectiveTwistSectorCoordinates_reconstruct (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    ∑ J ∈ s.powerset, ((projectiveTwistSectorCoordinates n s i hi j d a).val.val J).val
      ⟨Laurent.SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩ =
      (projectiveTwistConeCoordinates n s i hi j d a).val.val x :=
  Laurent.SectorNew.Dolbeault.laurentSectorEquiv_reconstruct s (projectiveTwistConeCoordinates n s i hi j d a).val x

end

section

/-! The actual projective point associated to a nonzero homogeneous coordinate vector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Set

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

theorem laurentConeVector_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) : x.val ≠ 0 := by
  obtain ⟨i, hi⟩ := hs
  intro hx
  exact (Laurent.SectorTo.Dolbeault.mem_laurentCoordinateDomain s x.val).mp x.property i hi (congrFun hx i)

def projectiveConePoint (n : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) : Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s :=
  ⟨(ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n)
      (Projectivization.mk ℂ x.val (laurentConeVector_ne_zero s hs x)), by
    change (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n)
      (Projectivization.mk ℂ x.val (laurentConeVector_ne_zero s hs x))) ∈ Projective.IntersectionDomains.Dolbeault.projectivePatchIntersection s
    rw [Homeomorph.symm_apply_apply]
    intro i hi
    exact (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i x.val _).mpr ((Laurent.SectorTo.Dolbeault.mem_laurentCoordinateDomain s x.val).mp x.property i hi)⟩

theorem projectiveConePoint_ratio (n : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) (i j : Fin (n + 1)) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (projectiveConePoint n s hs x).val) =
      x.val j / x.val i := by
  change Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n)
    (Projectivization.mk ℂ x.val (laurentConeVector_ne_zero s hs x)))) = _
  rw [Homeomorph.symm_apply_apply, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio_mk]

theorem projectiveConePoint_chart (n : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (i : Fin (n + 1)) (hi : i ∈ s) (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi (projectiveConePoint n s hs x)).val =
      Laurent.ConeCoordinates.Dolbeault.laurentConeRatios i x.val := by
  funext j
  rw [Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart_apply, projectiveConePoint_ratio]
  rfl

theorem projectiveConePoint_chart_symm (n : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (i : Fin (n + 1)) (hi : i ∈ s) (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi).symm
      ⟨Laurent.ConeCoordinates.Dolbeault.laurentConeRatios i x.val,
        (projectiveIntersectionProduct_eq_laurentAffineDomain s i).ge
          (Laurent.ConeCoordinates.Dolbeault.laurentConeNormalize s i hi x).property⟩ = projectiveConePoint n s hs x := by
  have h : Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi (projectiveConePoint n s hs x) =
      ⟨Laurent.ConeCoordinates.Dolbeault.laurentConeRatios i x.val,
        (projectiveIntersectionProduct_eq_laurentAffineDomain s i).ge
          (Laurent.ConeCoordinates.Dolbeault.laurentConeNormalize s i hi x).property⟩ :=
    Subtype.ext (projectiveConePoint_chart n s hs i hi x)
  exact (congrArg (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi).symm h.symm).trans
    ((Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi).symm_apply_apply _)

end

/-! Cone coordinates evaluate the original twist frame at the actual projective point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistConeCoordinates_evaluate (n : ℕ) (s : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)))
    (x : Laurent.SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (projectiveTwistConeCoordinates n s i hi j d a).val.val x = x.val i ^ d *
      (show DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
        (M := Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) from
          SectionCoordinates.Dolbeault.projectiveTwistSectionFrame n s i hi j d a).val (projectiveConePoint n s hs x) := by
  rw [projectiveTwistConeCoordinates_apply, SectionCoordinates.Dolbeault.projectiveTwistSectionCoordinates_apply,
    projectiveConePoint_chart_symm n s hs i hi x]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.Cone.Dolbeault
