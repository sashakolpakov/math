import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.IntegralComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

/-! # Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Composition of actual crystalline pullbacks and commutation with the native finite-field Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

section

variable (q : ℕ) [Fact q.Prime]
  {X Y Z : Over (Spec (CommRingCat.of (ZMod q)))}

theorem Crystalline.Composition.rationalPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Crystalline.CoefficientAdapter.rationalPullback q f).comp (Crystalline.CoefficientAdapter.rationalPullback q g) = Crystalline.CoefficientAdapter.rationalPullback q (f ≫ g) := by
  apply LinearMap.ext
  intro x
  change Crystalline.CoefficientAdapter.rationalPullback q f (Crystalline.CoefficientAdapter.rationalPullback q g x) = Crystalline.CoefficientAdapter.rationalPullback q (f ≫ g) x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    exact congrArg (fun z => a ⊗ₜ[Crystalline.CoefficientAdapter.Witt q] z)
      (Crystalline.IntegralComposition.integralPullback_comp f.left (by simp only [Crystalline.CoefficientAdapter.wittStructure, ← Category.assoc, Over.w])
        g.left (by simp only [Crystalline.CoefficientAdapter.wittStructure, ← Category.assoc, Over.w]) 1 x)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Crystalline.Composition.rationalPullback_frobenius (f : X ⟶ Y) :
    (Crystalline.CoefficientAdapter.rationalPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X)).comp (Crystalline.CoefficientAdapter.rationalPullback q f) =
      (Crystalline.CoefficientAdapter.rationalPullback q f).comp (Crystalline.CoefficientAdapter.rationalPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) Y)) :=
  (Crystalline.Composition.rationalPullback_comp q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) f).trans
    ((congrArg (Crystalline.CoefficientAdapter.rationalPullback q) (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius_naturality (ZMod q) X f)).trans
      (Crystalline.Composition.rationalPullback_comp q f (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) Y)).symm)

end

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.crystallineFrobenius_commutes (f : A.ExtendingEndomorphism) :
    A.crystallineFrobenius.comp (A.crystallinePullback f) =
      (A.crystallinePullback f).comp A.crystallineFrobenius :=
  Crystalline.Composition.rationalPullback_frobenius q (A.specialEndomorphism f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
