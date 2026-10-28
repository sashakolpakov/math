import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainCycle
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent

/-! # Cech Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf

noncomputable section

/-! The actual direct Čech functor preserves kernels degreewise and corrects lifted cochains using vanishing in the next degree. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens)

def functor : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) ⥤
    CochainComplex (ModuleCat.{u} R) ℕ :=
  sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) ⋙
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U

instance functor_additive : (functor R X U).Additive := by
  change (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) ⋙
    FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

instance degree_preservesLimits (n : ℕ) : PreservesLimits
    (functor R X U ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n) := by
  change PreservesLimits
    (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R) ⋙
      (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n))
  infer_instance

variable (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)))

theorem degree_exact (hS : S.Exact) [Mono S.f] (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.CochainCycle.CochainCycleCorrection.degree R (S.map (functor R X U)) n).Exact :=
  hS.map_of_mono_of_preservesKernel
    (functor R X U ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n)
    inferInstance inferInstance

instance degree_mono [Mono S.f] (n : ℕ) : Mono (((functor R X U).map S.f).f n) := by
  change Mono ((functor R X U ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map S.f)
  infer_instance

theorem exists_corrected_cycle (hS : S.Exact) [Mono S.f] (n : ℕ)
    (hA : ((functor R X U).obj S.X₁).ExactAt (n + 1))
    (y : ((functor R X U).obj S.X₂).X n)
    (hy : ((functor R X U).map S.g).f (n + 1)
      (((functor R X U).obj S.X₂).d n (n + 1) y) = 0) :
    ∃ y' : ((functor R X U).obj S.X₂).X n,
      ((functor R X U).obj S.X₂).d n (n + 1) y' = 0 ∧
        ((functor R X U).map S.g).f n y' = ((functor R X U).map S.g).f n y := by
  have : Mono ((S.map (functor R X U)).f.f (n + 2)) := degree_mono R X U S (n + 2)
  exact AlgebraicGeometry.Crystalline.Cohomology.CochainCycle.CochainCycleCorrection.exists_cycle R (S.map (functor R X U)) n
    (degree_exact R X U S hS (n + 1))
    ((HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mp hA) y hy

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf
