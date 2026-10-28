import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.IntersectionFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StandardFunctionSheaf

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SectionCoordinates.Dolbeault

noncomputable section

/-! Coordinates of actual analytified twist sections on a standard projective
intersection. The maps evaluate the original unit frame, then compose with the
inverse of the actual projective coordinate chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

section BiholomorphicFunctions

variable {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

def holomorphicBiholomorphFunctionEquiv (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ e)
    (he' : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, E) ∞ e.symm) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M) ≃ₐ[ℂ]
      DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := F) (M := N) where
  toFun f := ⟨fun y => f (e.symm y), f.contMDiff.comp he'⟩
  invFun g := ⟨fun x => g (e x), g.contMDiff.comp he⟩
  left_inv f := by
    apply ContMDiffMap.ext
    intro x
    exact congrArg f (e.symm_apply_apply x)
  right_inv g := by
    apply ContMDiffMap.ext
    intro y
    exact congrArg g (e.apply_symm_apply y)
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

end BiholomorphicFunctions

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveIntersectionFunctionCoordinates (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
        (M := Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) ≃ₐ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions
        (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (Projective.IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i)) :=
  (holomorphicBiholomorphFunctionEquiv (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi)
    (Projective.IntersectionHolomorphy.Dolbeault.projectiveSchemeIntersectionChart_holomorphic n s i hi)
    (Projective.IntersectionHolomorphy.Dolbeault.projectiveSchemeIntersectionChart_symm_holomorphic n s i hi)).trans
      (Holomorphic.StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv
        ({k : Fin (n + 1) // k ≠ i} → ℂ) _).symm

def projectiveTwistSectionFrame (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) ≃ₗ[
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).obj.obj
        (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s))]
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).obj.obj
        (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) :=
  Open.UnitFrame.Dolbeault.openUnitFrameSectionEquiv _ _ _ (IntersectionFrames.Dolbeault.projectiveAnalytifiedTwist_intersectionUnitIso n s i hi j d)

def projectiveTwistSectionCoordinates (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ) :
    (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)) ≃+
      Holomorphic.FunctionPure.holomorphicFunctions
        (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (Projective.IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i)) :=
  (projectiveTwistSectionFrame n s i hi j d).toAddEquiv.trans
    (projectiveIntersectionFunctionCoordinates n s i hi).toAddEquiv

theorem projectiveTwistSectionCoordinates_apply (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)))
    (z : ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct (Projective.IntersectionDomains.Dolbeault.projectiveIntersectionPunctures s i)) :
    (projectiveTwistSectionCoordinates n s i hi j d a).val z =
      (show DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := RegularSmoothness.NativeModel (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))
        (M := Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s) from
          projectiveTwistSectionFrame n s i hi j d a).val
            ((Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersectionChart n s i hi).symm z) := rfl

theorem projectiveTwistSectionCoordinates_smul (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (j : Fin (n + 1)) (d : ℤ)
    (r : (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).obj.obj
      (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s)))
    (a : (Analytification.Dolbeault.projectiveAnalytifiedTwist n j d).val.obj (op (Projective.IntersectionDomains.Dolbeault.projectiveSchemeIntersection n s))) :
    projectiveTwistSectionCoordinates n s i hi j d (r • a) =
      projectiveIntersectionFunctionCoordinates n s i hi r *
        projectiveTwistSectionCoordinates n s i hi j d a := by
  change projectiveIntersectionFunctionCoordinates n s i hi
      (projectiveTwistSectionFrame n s i hi j d (r • a)) = _
  rw [map_smul]
  exact (projectiveIntersectionFunctionCoordinates n s i hi).map_mul r _

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.SectionCoordinates.Dolbeault
