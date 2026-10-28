import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.IsomorphismNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelUniversalIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.ParameterPointMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsomorphismUniversalPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor

/-! # Universal Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.UniversalMap

noncomputable section

/-! The complete universal moduli isomorphism and all its specializations recover exactly the underlying bounded abelian isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

theorem boundedPolarizedLevelUniversalIso_abelian_hom
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) :
    (Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIso A B j P PB PD PE).abelian.hom =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P)
        (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom := by
  let c := Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P
  have H := Moduli.Isomorphisms.LevelPreservingIso.fromIteratedParameterPoint_abelian_hom A B c
    (Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIteratedIso A B j P PB PD PE)
  change (Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIso A B j P PB PD PE).abelian.hom =
    HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackMorphism c ((Over.pullback c.left).map (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom) at H
  have hc : HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackMorphism c
      ((Over.pullback c.left).map (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom) =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom := by
    unfold HilbertConstruction.Over.BaseMapPullback.overBaseMapPullbackMorphism Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange
    rw [ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter, ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter]
  exact H.trans hc

theorem boundedPolarizedLevelUniversalIso_point_abelian
    (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme) (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme)
    (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme) {T : Over S}
    (c : T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) :
    (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint A B c (Bounded.PolarizedLevelUniversalIsomorphism.boundedPolarizedLevelUniversalIso A B j P PB PD PE)).abelian.hom =
      (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A.abelian B.abelian j P T
        (c ≫ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P)).val.val.val :=
  (Moduli.Isomorphisms.LevelPreservingIso.atParameterPoint_abelian_hom A B c _).trans
    ((congrArg (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c)
      (boundedPolarizedLevelUniversalIso_abelian_hom A B j P PB PD PE)).trans
      ((Geometric.MorphismFunctor.geometricFamilyMorphismBaseChange_composition c (Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P)
        (Bounded.UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom).trans
        (Bounded.IsomorphismUniversalPoints.boundedAbelianUniversalIso_point A.abelian B.abelian j P _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.UniversalMap
