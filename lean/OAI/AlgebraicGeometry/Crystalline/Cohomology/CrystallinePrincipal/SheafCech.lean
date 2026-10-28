import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainCycle
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalPrimitives
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech

/-! # Sheaf Cech -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech

noncomputable section

/-!
# Kernel preservation and correction in native sheaf Čech cochains

Native sheaves restrict to the actual principal coefficient diagram.
Each degree of its Čech functor preserves limits. Thus a left exact
sequence of native sheaves is left exact on cochains, and vanishing in
the next Čech degree supplies the correction of any lifted cochain.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def coefficients : Sheaf J V ⥤ (Cᵒᵖ ⥤ V) :=
  sheafToPresheaf J V ⋙
    (Functor.whiskeringLeft _ _ V).obj (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).op

instance coefficients_additive : (coefficients p k X Q).Additive := by
  dsimp [coefficients]
  infer_instance

instance coefficients_preservesLimits : PreservesLimits (coefficients p k X Q) := by
  dsimp [coefficients]
  infer_instance

variable {ι : Type u} (s : ι → Q.thickening.ring)

def functor : Sheaf J V ⥤ CochainComplex V ℕ :=
  coefficients p k X Q ⋙ cechComplexFunctor.{u, u, u + 1, u, u + 2}
    (A := V) (Cech.CrystallinePrincipalCech.family s)

instance functor_additive : (functor p k X Q s).Additive := by
  change (coefficients p k X Q ⋙ FormalCoproduct.cochainComplexFunctor.{u, u, u + 1, u, u + 2} (A := V)
    (FormalCoproduct.mk ι (Cech.CrystallinePrincipalCech.family s)).cech).Additive
  infer_instance

instance degree_preservesLimits (n : ℕ) :
    PreservesLimits (functor p k X Q s ⋙ HomologicalComplex.eval V (ComplexShape.up ℕ) n) := by
  change PreservesLimits (coefficients p k X Q ⋙
    (FormalCoproduct.cochainComplexFunctor.{u, u, u + 1, u, u + 2} (A := V)
      (FormalCoproduct.mk ι (Cech.CrystallinePrincipalCech.family s)).cech ⋙
        HomologicalComplex.eval V (ComplexShape.up ℕ) n))
  infer_instance

def shortComplex (S : ShortComplex (Sheaf J V)) : ShortComplex (CochainComplex V ℕ) :=
  S.map (functor p k X Q s)

theorem degree_exact (S : ShortComplex (Sheaf J V)) (hS : S.Exact) [Mono S.f] (n : ℕ) :
    (CochainCycle.CochainCycleCorrection.degree (Site.CoefficientRing p k) (shortComplex p k X Q s S) n).Exact :=
  hS.map_of_mono_of_preservesKernel
    (functor p k X Q s ⋙ HomologicalComplex.eval V (ComplexShape.up ℕ) n) inferInstance inferInstance

instance degree_mono (S : ShortComplex (Sheaf J V)) [Mono S.f] (n : ℕ) :
    Mono ((shortComplex p k X Q s S).f.f n) := by
  change Mono ((functor p k X Q s ⋙ HomologicalComplex.eval V (ComplexShape.up ℕ) n).map S.f)
  infer_instance

theorem exists_corrected_cycle (S : ShortComplex (Sheaf J V)) (hS : S.Exact) [Mono S.f]
    (n : ℕ) (hA : ((functor p k X Q s).obj S.X₁).ExactAt (n + 1))
    (y : ((functor p k X Q s).obj S.X₂).X n)
    (hy : ((functor p k X Q s).map S.g).f (n + 1)
      (((functor p k X Q s).obj S.X₂).d n (n + 1) y) = 0) :
    ∃ y' : ((functor p k X Q s).obj S.X₂).X n,
      ((functor p k X Q s).obj S.X₂).d n (n + 1) y' = 0 ∧
        ((functor p k X Q s).map S.g).f n y' = ((functor p k X Q s).map S.g).f n y := by
  apply CochainCycle.CochainCycleCorrection.exists_cycle (Site.CoefficientRing p k)
    (shortComplex p k X Q s S) n (degree_exact p k X Q s S hS (n + 1))
      ((HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mp hA) y hy

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech
