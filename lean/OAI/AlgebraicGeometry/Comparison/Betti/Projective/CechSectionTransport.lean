import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechCoordinates
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr

/-! # Cech Section Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechSectionTransport.Dolbeault

noncomputable section

/-! Transport between the native categorical Čech intersection and its actual
algebraic-open analytification commutes with every cosimplicial restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped Simplicial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTupleRange_precomp_subset (n a b : ℕ)
    (t : Fin (b + 1) → Fin (n + 1)) (f : Fin (a + 1) → Fin (b + 1)) :
    Finset.univ.image (t ∘ f) ⊆ Finset.univ.image t := by
  intro i hi
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_image.mpr ⟨f k, Finset.mem_univ _, rfl⟩

def projectiveCechOpenSectionIso (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1)) :
    (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
        (op (∏ᶜ fun k : Fin (q + 1) => Intersections.Dolbeault.projectiveStandardCover n (t k))) ≅
      (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj (op (Open.AffineIsoEvaluation.analyticOpen (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
        (Intersections.Dolbeault.projectiveAlgebraicIntersection n (Finset.univ.image t)))) :=
  (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.mapIso
    (eqToIso (congrArg op (ProjectiveTwist.CechCoordinates.Dolbeault.projectiveCechIntersection_eq_analyticOpen n q t)))

theorem projectiveTwistCechSectionCoordinates_function (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (t : Fin (q + 1) → Fin (n + 1))
    (a : (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.obj
      (op (∏ᶜ fun k : Fin (q + 1) => Intersections.Dolbeault.projectiveStandardCover n (t k)))) :
    ProjectiveTwist.CechCoordinates.Dolbeault.projectiveTwistCechSectionCoordinates n j d q t a =
      ProjectiveTwist.IntersectionMaps.Dolbeault.projectiveTwistIntersectionFunction n (Finset.univ.image t) (t 0)
        (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩) j d
        ((projectiveCechOpenSectionIso n j d q t).hom a) := rfl

theorem projectiveCechOpenSectionIso_precomp (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    {a b : SimplexCategory} (f : a ⟶ b) (t : Fin (b.len + 1) → Fin (n + 1)) :
    (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map
        (((FormalCoproduct.mk _ (Intersections.Dolbeault.projectiveStandardCover n)).mapPower f.toOrderHom).φ t).op ≫
        (projectiveCechOpenSectionIso n j d b.len t).hom =
      (projectiveCechOpenSectionIso n j d a.len (t ∘ f.toOrderHom)).hom ≫
        (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map (homOfLE (Open.SmoothForms.analyticOpen_mono
          (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (IntersectionInclusions.Dolbeault.projectiveAlgebraicIntersection_antitone n
            (projectiveTupleRange_precomp_subset n a.len b.len t f.toOrderHom)))).op := by
  change (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map _ ≫
      (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map _ =
    (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map _ ≫ (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map _
  exact ((ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map_comp _ _).symm.trans
    ((congrArg (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map (Subsingleton.elim _ _)).trans
      ((ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj.map_comp _ _))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechSectionTransport.Dolbeault
