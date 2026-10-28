import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.IsomorphismFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.YonedaPoints
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Classifying Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ClassifyingMap

noncomputable section

/-! The complete universal isomorphism defines a natural injective map from the constructed parameter's points to the bounded moduli-isomorphism functor. Surjectivity remains a separate step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedPolarizedLevelUniversalBoundedIso
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    IsomorphismFunctor.BoundedFamilyLevelIso A B j P (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) := by
  refine ⟨Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIso A B j P PB PD PE, ?_⟩
  let c := Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P
  have H := (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P _ c).val.val.property
  have he := (UniversalMap.boundedPolarizedLevelUniversalIso_abelian_hom A B j P PB PD PE).trans
    (Bounded.IsomorphismUniversalPoints.boundedAbelianUniversalIso_point A.abelian B.abelian j P c)
  exact he.symm ▸ H

def boundedPolarizedLevelClassifyingMap
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    yoneda.obj (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) ⟶ IsomorphismFunctor.boundedFamilyLevelIsoFunctor A B j P :=
  yonedaEquiv.symm (boundedPolarizedLevelUniversalBoundedIso A B j P PB PD PE)

theorem boundedPolarizedLevelUniversalBoundedIso_val
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    (boundedPolarizedLevelUniversalBoundedIso A B j P PB PD PE).val =
      Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIso A B j P PB PD PE := by
  simp only [boundedPolarizedLevelUniversalBoundedIso]

theorem boundedPolarizedLevelClassifyingMap_point
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) {T : Over S}
    (c : T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) :
    ((boundedPolarizedLevelClassifyingMap A B j P PB PD PE).app (.op T) c).val =
      PointMap.boundedPolarizedLevelUniversalPointMap A B j P PB PD PE T c := by
  unfold boundedPolarizedLevelClassifyingMap PointMap.boundedPolarizedLevelUniversalPointMap
  exact (YonedaPoints.boundedFamilyLevelIso_yoneda_point A B j P
    (boundedPolarizedLevelUniversalBoundedIso A B j P PB PD PE) c).trans
      (congrArg (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c)
        (boundedPolarizedLevelUniversalBoundedIso_val A B j P PB PD PE))

theorem boundedPolarizedLevelClassifyingMap_abelian
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) {T : Over S}
    (c : T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) :
    ((boundedPolarizedLevelClassifyingMap A B j P PB PD PE).app (.op T) c).val.abelian.hom =
      (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P T
        (c ≫ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P)).val.val.val :=
  (congrArg (fun z : Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (B.pullback T.hom) => z.abelian.hom)
    (boundedPolarizedLevelClassifyingMap_point A B j P PB PD PE c)).trans
      (PointMap.boundedPolarizedLevelUniversalPointMap_abelian A B j P PB PD PE T c)

theorem boundedPolarizedLevelClassifyingMap_mono
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    Mono (boundedPolarizedLevelClassifyingMap A B j P PB PD PE) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro c d h
  apply PointFaithfulness.boundedPolarizedLevelUniversalIso_points_injective A B j P PB PD PE T.unop
  exact (boundedPolarizedLevelClassifyingMap_point A B j P PB PD PE c).symm.trans
    ((congrArg Subtype.val h).trans (boundedPolarizedLevelClassifyingMap_point A B j P PB PD PE d))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ClassifyingMap
