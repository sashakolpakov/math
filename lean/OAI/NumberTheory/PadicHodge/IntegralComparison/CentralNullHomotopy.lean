import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
import Mathlib.Algebra.Homology.Linear

/-! # Central Null Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CentralNullHomotopy

noncomputable section

/-! A scalar nullhomotopy on a source kills maps into a complex where
that same scalar has an actual inverse. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
universe u v w
variable (R : Type u) [CommRing R]
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
  {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}

def of_inverse (a : R) (hK : Homotopy (a • 𝟙 K) 0)
    (b : L ⟶ L) (hb : a • b = 𝟙 L) (f : K ⟶ L) : Homotopy f 0 :=
  (Homotopy.ofEq (by
    calc f = f ≫ (a • b) := by rw [hb, Category.comp_id]
      _ = (a • 𝟙 K) ≫ (f ≫ b) := by
        rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp])).trans
    ((hK.compRight (f ≫ b)).trans (Homotopy.ofEq (zero_comp)))

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c)

theorem dual_scalar (a : R) : DualComplexHomology.map R (a • 𝟙 K) =
    a • 𝟙 (DualComplexHomology.complex R K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  exact φ.map_smul a x

def dual (a : R) (h : Homotopy (a • 𝟙 K) 0) :
    Homotopy (a • 𝟙 (DualComplexHomology.complex R K)) 0 :=
  (Homotopy.ofEq (dual_scalar R K a).symm).trans
    (((ExactModuleDualFunctor.functor R).mapHomotopy h.op).trans
      (Homotopy.ofEq (by
        apply HomologicalComplex.Hom.ext
        funext i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply LinearMap.ext
        intro x
        exact φ.map_zero)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CentralNullHomotopy
