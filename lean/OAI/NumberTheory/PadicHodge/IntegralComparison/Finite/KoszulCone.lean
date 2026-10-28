import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulCone
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix
import Mathlib.Data.List.OfFn

/-! # Koszul Cone -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.KoszulCone

noncomputable section

/-! The last-coordinate decomposition of the finite exterior Koszul complex. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.GeneratorMatrix

universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def includeInit : (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
  LinearMap.pi (Fin.lastCases 0 (fun i => LinearMap.proj i))

def projectInit : (Fin (n + 1) → R) →ₗ[R] (Fin n → R) :=
  LinearMap.pi (fun i => LinearMap.proj i.castSucc)

def lastVector : Fin (n + 1) → R := Pi.single (Fin.last n) 1

@[simp] theorem includeInit_castSucc (v : Fin n → R) (i : Fin n) :
    includeInit R n v i.castSucc = v i := by simp [includeInit]

@[simp] theorem includeInit_last (v : Fin n → R) :
    includeInit R n v (Fin.last n) = 0 := by simp [includeInit]

@[simp] theorem projectInit_apply (v : Fin (n + 1) → R) (i : Fin n) :
    projectInit R n v i = v i.castSucc := rfl

@[simp] theorem lastVector_last : lastVector R n (Fin.last n) = 1 := by
  simp [lastVector]

@[simp] theorem lastVector_castSucc (i : Fin n) : lastVector R n i.castSucc = 0 := by
  simp [lastVector, ne_of_lt i.castSucc_lt_last]

theorem project_include : (projectInit R n).comp (includeInit R n) = LinearMap.id := by
  ext v i
  simp

theorem include_project : (includeInit R n).comp (projectInit R n) =
    Exterior.CoordinateSplit.projection R (Fin (n + 1) → R)
      (LinearMap.proj (Fin.last n)) (lastVector R n) := by
  apply LinearMap.ext
  intro v
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Exterior.CoordinateSplit.projection_apply]
  · simp [Exterior.CoordinateSplit.projection_apply]

theorem last_include : (LinearMap.proj (Fin.last n)).comp (includeInit R n) = 0 := by
  ext v
  simp

theorem project_last : projectInit R n (lastVector R n) = 0 := by
  funext i
  simp

theorem equation_include (s : Fin (n + 1) → R) :
    (Koszul.GeneratorMatrix.equation R s).comp (includeInit R n) = Koszul.GeneratorMatrix.equation R (s ∘ Fin.castSucc) := by
  apply LinearMap.ext
  intro v
  simp [Koszul.GeneratorMatrix.equation_apply, Fin.sum_univ_castSucc]

theorem equation_last (s : Fin (n + 1) → R) :
    Koszul.GeneratorMatrix.equation R s (lastVector R n) = s (Fin.last n) := by
  simp [Koszul.GeneratorMatrix.equation_apply, Fin.sum_univ_castSucc]

def iso (s : Fin (n + 1) → R) :
    homotopyCofiber (s (Fin.last n) •
      𝟙 (Exterior.KoszulComplex.complex R (Fin n → R) (Koszul.GeneratorMatrix.equation R (s ∘ Fin.castSucc)))) ≅
        Exterior.KoszulComplex.complex R (Fin (n + 1) → R) (Koszul.GeneratorMatrix.equation R s) := by
  rw [← equation_last R n s]
  exact Exterior.KoszulCone.iso R (Fin (n + 1) → R) (Koszul.GeneratorMatrix.equation R s)
    (LinearMap.proj (Fin.last n)) (lastVector R n) (Fin n → R)
    (Koszul.GeneratorMatrix.equation R (s ∘ Fin.castSucc)) (includeInit R n) (projectInit R n)
    (equation_include R n s) (project_include R n) (include_project R n)
    (lastVector_last R n) (last_include R n) (project_last R n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.KoszulCone
