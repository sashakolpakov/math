import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorAcyclic
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.ComparisonByPresentations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Annihilator
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler

/-! # Diagonal Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTor

noncomputable section

/-! Reduction to the diagonal for native Tor over a Noetherian algebra
over a field. It preserves every Tor length and hence every Euler cutoff. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTensorNaturality

variable (K R : Type u) [Field K] [CommRing R] [Algebra K R]

attribute [local instance] DiagonalTensor.diagonalAlgebra

variable (M N : ModuleCat.{u} R)

abbrev external : ModuleCat.{u} (DiagonalTensor.Ring K R) := (ExternalTensorFunctor.tensor K R R N).obj M

theorem exists_iso [IsNoetherianRing R] [Module.Finite R M] (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars (DiagonalTensorNaturality.first K R)).obj
      (((Tor (ModuleCat (DiagonalTensor.Ring K R)) n).obj (external K R M N)).obj (DiagonalTensorNaturality.diagonal K R)) ≅
      (((Tor (ModuleCat R) n).obj M).obj N)) :=
  ProjectionFormula.Tor.ComparisonByPresentations.exists_iso R (DiagonalTensor.Ring K R) N (DiagonalTensorNaturality.diagonal K R)
    (ExternalTensorFunctor.tensor K R R N) (ModuleCat.restrictScalars (DiagonalTensorNaturality.first K R))
    (DiagonalTensorNaturality.naturalIso K R N) (fun P _ _ i => ExternalTensorAcyclic.free K R N P i) n M

theorem length_restrict (n : ℕ) :
    Module.length (DiagonalTensor.Ring K R) (((Tor (ModuleCat (DiagonalTensor.Ring K R)) n).obj (external K R M N)).obj (DiagonalTensorNaturality.diagonal K R)) =
      Module.length R ((ModuleCat.restrictScalars (DiagonalTensorNaturality.first K R)).obj
        (((Tor (ModuleCat (DiagonalTensor.Ring K R)) n).obj (external K R M N)).obj (DiagonalTensorNaturality.diagonal K R))) := by
  let T := (((Tor (ModuleCat (DiagonalTensor.Ring K R)) n).obj (external K R M N)).obj (DiagonalTensorNaturality.diagonal K R))
  let : Module R T := Module.compHom T (DiagonalTensorNaturality.first K R)
  let : IsScalarTower (DiagonalTensor.Ring K R) R T := IsScalarTower.of_algebraMap_smul fun t x => by
    change DiagonalTensorNaturality.first K R (DiagonalTensor.multiplication K R t) • x = t • x
    have h := ProjectionFormula.Tor.Annihilator.second (DiagonalTensor.Ring K R) (external K R M N) (DiagonalTensorNaturality.diagonal K R)
      (t - DiagonalTensorNaturality.first K R (DiagonalTensor.multiplication K R t)) (by
        intro y
        change (DiagonalTensor.multiplication K R (t - DiagonalTensorNaturality.first K R (DiagonalTensor.multiplication K R t))) * (show R from y) = 0
        have he : DiagonalTensor.multiplication K R (DiagonalTensorNaturality.first K R (DiagonalTensor.multiplication K R t)) = DiagonalTensor.multiplication K R t := mul_one _
        rw [map_sub, he, sub_self, zero_mul]) n x
    rw [sub_smul, sub_eq_zero] at h
    exact h.symm
  exact Module.length_eq_of_surjective (R := R) (S := DiagonalTensor.Ring K R) (M := T)
    (fun r => ⟨DiagonalTensorNaturality.first K R r, (mul_one r : DiagonalTensor.multiplication K R (DiagonalTensorNaturality.first K R r) = r)⟩)

theorem length [IsNoetherianRing R] [Module.Finite R M] (n : ℕ) :
    Module.length (DiagonalTensor.Ring K R) (((Tor (ModuleCat (DiagonalTensor.Ring K R)) n).obj (external K R M N)).obj (DiagonalTensorNaturality.diagonal K R)) =
      Module.length R (((Tor (ModuleCat R) n).obj M).obj N) :=
  (length_restrict K R M N n).trans (Classical.choice (exists_iso K R M N n)).toLinearEquiv.length_eq

theorem euler [IsNoetherianRing R] [Module.Finite R M] (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler (DiagonalTensor.Ring K R) (external K R M N) (DiagonalTensorNaturality.diagonal K R) d = ProjectionFormula.Tor.Euler.euler R M N d := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ i * (l.toNat : ℚ)) (DiagonalTor.length K R M N i)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DiagonalTor
