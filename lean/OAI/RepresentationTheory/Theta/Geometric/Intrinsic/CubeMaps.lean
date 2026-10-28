import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubicalEmbedding
import OAI.RepresentationTheory.Theta.Geometric.Cubical.Arguments

/-! # Cube Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeMaps

noncomputable section

/-! The actual projections and sum maps on the triple product, together
with their exact formulas under the original period comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

def nativeCubeProjection (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Fin 3 → ((AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A).toOver ⟶ A.toOver) :=
  ![fst (A.toOver ⊗ A.toOver) A.toOver ≫ fst A.toOver A.toOver,
    fst (A.toOver ⊗ A.toOver) A.toOver ≫ snd A.toOver A.toOver,
    snd (A.toOver ⊗ A.toOver) A.toOver]

def nativeCubePositiveMap (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Fin 4 → ((AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A).toOver ⟶ A.toOver) :=
  ![nativeCubeProjection A 0 * nativeCubeProjection A 1 * nativeCubeProjection A 2,
    nativeCubeProjection A 0, nativeCubeProjection A 1, nativeCubeProjection A 2]

def nativeCubeNegativeMap (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Fin 3 → ((AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A A) A).toOver ⟶ A.toOver) :=
  ![nativeCubeProjection A 0 * nativeCubeProjection A 1,
    nativeCubeProjection A 0 * nativeCubeProjection A 2,
    nativeCubeProjection A 1 * nativeCubeProjection A 2]

theorem nativeCubePositiveMap_period (Φ : Torus.Data.CM.ProjectivePeriodData) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) (k : Fin 4) (z : Φ.triple.space) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (nativeCubePositiveMap A k)
      (lift (lift (e (QuotientAddGroup.mk z.1.1)) (e (QuotientAddGroup.mk z.1.2)))
        (e (QuotientAddGroup.mk z.2))) =
      e (QuotientAddGroup.mk (Φ.cubePositiveArgument k z)) := by
  rcases z with ⟨⟨u, v⟩, w⟩
  fin_cases k <;>
    simp [nativeCubePositiveMap, nativeCubeProjection, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map, MonObj.comp_mul,
      Torus.Data.CM.ProjectivePeriodData.cubePositiveArgument,
      Torus.Data.CM.ProjectivePeriodData.tripleFirst, Torus.Data.CM.ProjectivePeriodData.tripleSecond,
      Torus.Data.CM.ProjectivePeriodData.tripleThird, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ← Category.assoc, lift_fst, lift_snd, he]
  · exact congrArg (fun q => e (QuotientAddGroup.mk u) * e (QuotientAddGroup.mk v) * q)
      (lift_snd (lift (e (QuotientAddGroup.mk u)) (e (QuotientAddGroup.mk v)))
        (e (QuotientAddGroup.mk w)))
  · rfl
  · rfl
  · exact lift_snd (lift (e (QuotientAddGroup.mk u)) (e (QuotientAddGroup.mk v)))
      (e (QuotientAddGroup.mk w))

theorem nativeCubeNegativeMap_period (Φ : Torus.Data.CM.ProjectivePeriodData) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) (k : Fin 3) (z : Φ.triple.space) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (nativeCubeNegativeMap A k)
      (lift (lift (e (QuotientAddGroup.mk z.1.1)) (e (QuotientAddGroup.mk z.1.2)))
        (e (QuotientAddGroup.mk z.2))) =
      e (QuotientAddGroup.mk (Φ.cubeNegativeArgument k z)) := by
  rcases z with ⟨⟨u, v⟩, w⟩
  fin_cases k <;>
    simp [nativeCubeNegativeMap, nativeCubeProjection, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map, MonObj.comp_mul,
      Torus.Data.CM.ProjectivePeriodData.cubeNegativeArgument,
      Torus.Data.CM.ProjectivePeriodData.tripleFirst, Torus.Data.CM.ProjectivePeriodData.tripleSecond,
      Torus.Data.CM.ProjectivePeriodData.tripleThird, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ← Category.assoc, lift_fst, lift_snd, he]
  · rfl
  · exact congrArg (fun q => e (QuotientAddGroup.mk u) * q)
      (lift_snd (lift (e (QuotientAddGroup.mk u)) (e (QuotientAddGroup.mk v)))
        (e (QuotientAddGroup.mk w)))
  · exact congrArg (fun q => e (QuotientAddGroup.mk v) * q)
      (lift_snd (lift (e (QuotientAddGroup.mk u)) (e (QuotientAddGroup.mk v)))
        (e (QuotientAddGroup.mk w)))

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeMaps
