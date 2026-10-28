import OAI.ArithmeticGeometry.Descent.CMVariety.FiberGroupLaws

/-! # Family Power Maps -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints

noncomputable section

/-!
Construct actual algebraic power maps on the total space of an abelian
scheme and compare them with the given native fiber powers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left)

/-- The pointwise natural-power operation is an actual morphism of the
family's total scheme, obtained from its given group-scheme law. -/
def familyPowerMap (n : ℕ) : AbelianFamilyPoints.FamilyPoints.total S G ⟶ AbelianFamilyPoints.FamilyPoints.total S G :=
  Over.homMk ((𝟙 G.scheme) ^ n).left (by
    change ((𝟙 G.scheme) ^ n).left ≫ (G.scheme.hom ≫ S.hom) = G.scheme.hom ≫ S.hom
    rw [← Category.assoc, Over.w])

theorem familyPowerMap_fiber (n : ℕ) (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (u : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (G.pullback s.left).scheme) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (familyPowerMap S G n)
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) u) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion (AbelianFamilyPoints.FamilyPoints.projection S G) s) (u ^ n) := by
  let e := G.baseChangePointsMulEquiv s.left (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
  have hp := MonObj.comp_pow (𝟙 G.scheme) n (e u)
  rw [Category.comp_id] at hp
  have h := congrArg (fun w : G.Points ((Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) => w.left) hp
  have he := congrArg (fun w : G.Points ((Over.map s.left).obj (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) => w.left)
    (map_pow e u n)
  apply Over.OverMorphism.ext
  exact h.trans he.symm

theorem familyPowerMap_continuous (n : ℕ) :
    Continuous (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (familyPowerMap S G n)) :=
  AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FamilyPowerMaps.Abelian.FamilyPoints
