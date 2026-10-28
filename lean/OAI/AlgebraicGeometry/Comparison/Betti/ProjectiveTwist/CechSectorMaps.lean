import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ConeRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechSectionTransport
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr

/-! # Cech Sector Maps -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechSectorMaps.Dolbeault

noncomputable section

section

/-! Finite homogeneous Laurent sectors for the original projective Cech terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveTwistCechSectionSectors (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
        (op (∏ᶜ fun k : Fin (q + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n (t k))) ≃+
      HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies (Finset.univ.image t) d :=
  (Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d q t).addCommGroupIsoToAddEquiv.trans
    (Projective.ConeRestriction.Dolbeault.projectiveTwistAnalyticSectorCoordinates n (Finset.univ.image t) (t 0)
      (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d)

abbrev projectiveTwistCechSectorCochains (n : ℕ) (d : ℤ) (q : ℕ) :=
  ∀ t : Fin (q + 1) → Fin (n + 1), HomogeneousLaurent.Dolbeault.laurentHomogeneousSectorFamilies (Finset.univ.image t) d

def projectiveTwistCechSectors (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q ≃+
      projectiveTwistCechSectorCochains n d q :=
  (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj
    (Projective.Intersections.Dolbeault.projectiveStandardCover n) q).trans
      (AddEquiv.piCongrRight (projectiveTwistCechSectionSectors n j d q))

theorem projectiveTwistCechSectors_apply (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (a : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q)
    (t : Fin (q + 1) → Fin (n + 1)) :
    projectiveTwistCechSectors n j d q a t = projectiveTwistCechSectionSectors n j d q t
      (Pi.π (fun b : Fin (q + 1) → Fin (n + 1) =>
        (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
          (op (∏ᶜ fun k : Fin (q + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n (b k)))) t a) := by
  change projectiveTwistCechSectionSectors n j d q t
    (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj
      (Projective.Intersections.Dolbeault.projectiveStandardCover n) q a t) = _
  exact congrArg (projectiveTwistCechSectionSectors n j d q t)
    (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj
      (Projective.Intersections.Dolbeault.projectiveStandardCover n) q a t)

end

/-! All original projective Cech maps act by inclusion of the same Laurent sectors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistCechSectionSectors_map (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    {a b : SimplexCategory} (f : a ⟶ b) (t : Fin (b.len + 1) → Fin (n + 1))
    (z : (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
      (op (∏ᶜ fun k : Fin (a.len + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n ((t ∘ f.toOrderHom) k)))) :
    projectiveTwistCechSectionSectors n j d b.len t
        ((AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map
          (((FormalCoproduct.mk _ (Projective.Intersections.Dolbeault.projectiveStandardCover n)).mapPower f.toOrderHom).φ t).op z) =
      HomogeneousSectorSingle.Dolbeault.laurentHomogeneousFamilyInclusion
        (Projective.CechSectionTransport.Dolbeault.projectiveTupleRange_precomp_subset n a.len b.len t f.toOrderHom) d
        (projectiveTwistCechSectionSectors n j d a.len (t ∘ f.toOrderHom) z) := by
  have hm := ConcreteCategory.congr_hom (Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso_precomp n j d f t) z
  have h := Projective.ConeRestriction.Dolbeault.projectiveTwistAnalyticSectorCoordinates_restrict n
    (Projective.CechSectionTransport.Dolbeault.projectiveTupleRange_precomp_subset n a.len b.len t f.toOrderHom)
    (t 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    (t (f.toOrderHom 0)) (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d
    ((Projective.CechSectionTransport.Dolbeault.projectiveCechOpenSectionIso n j d a.len (t ∘ f.toOrderHom)).hom z)
  exact (congrArg (fun y : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op
      (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (Projective.Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)))) =>
    Projective.ConeRestriction.Dolbeault.projectiveTwistAnalyticSectorCoordinates n (Finset.univ.image t) (t 0)
      (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d y) hm).trans h

theorem projectiveTwistCechSectors_map (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    {a b : SimplexCategory} (f : a ⟶ b) (t : Fin (b.len + 1) → Fin (n + 1))
    (z : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X a.len) :
    projectiveTwistCechSectors n j d b.len
        ((((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ (Projective.Intersections.Dolbeault.projectiveStandardCover n)).cech).obj
          (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).map f) z) t =
      HomogeneousSectorSingle.Dolbeault.laurentHomogeneousFamilyInclusion
        (Projective.CechSectionTransport.Dolbeault.projectiveTupleRange_precomp_subset n a.len b.len t f.toOrderHom) d
        (projectiveTwistCechSectors n j d a.len z (t ∘ f.toOrderHom)) := by
  have ht := projectiveTwistCechSectors_apply n j d b.len
    ((((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ (Projective.Intersections.Dolbeault.projectiveStandardCover n)).cech).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).map f) z) t
  have hs := projectiveTwistCechSectors_apply n j d a.len z (t ∘ f.toOrderHom)
  have h := ConcreteCategory.congr_hom (AdditiveCechCoverCongr.additiveCechMap_proj
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj (Projective.Intersections.Dolbeault.projectiveStandardCover n) f t) z
  exact ht.trans ((congrArg (fun y : (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
      (op (∏ᶜ fun k : Fin (b.len + 1) => Projective.Intersections.Dolbeault.projectiveStandardCover n (t k))) =>
    projectiveTwistCechSectionSectors n j d b.len t y) h).trans
      ((projectiveTwistCechSectionSectors_map n j d f t _).trans
        (congrArg (HomogeneousSectorSingle.Dolbeault.laurentHomogeneousFamilyInclusion
          (Projective.CechSectionTransport.Dolbeault.projectiveTupleRange_precomp_subset n a.len b.len t f.toOrderHom) d) hs.symm)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechSectorMaps.Dolbeault
