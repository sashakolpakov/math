import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules

/-! # Hecke Exponents -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents

noncomputable section

/-! The three C0^i T_i elementary types. The active kernel has i
coordinates of exponent one; compact multiplicative kernels have all
three coordinates of exponent i. Thus the active level is q-torsion
while the common multiplier and compact level are q^i. -/

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules.Construction

def neighborLevel (i : Fin 3) : ℕ := i.val + 1

def activeExponents (i : Fin 3) (k : Fin 3) : ℕ :=
  if k.val < neighborLevel i then 1 else 0

def neighborExponents {s : ℕ} (active : Fin s) (multiplicative : Fin s → Bool)
    (i : Fin 3) (v : Fin s) (k : Fin 3) : ℕ :=
  if v = active then activeExponents i k else
    if multiplicative v then neighborLevel i else 0

theorem neighborExponents_bound {s : ℕ} (active : Fin s) (multiplicative : Fin s → Bool)
    (i : Fin 3) (v : Fin s) (k : Fin 3) :
    neighborExponents active multiplicative i v k ≤ neighborLevel i := by
  unfold neighborExponents activeExponents neighborLevel
  split_ifs <;> omega

theorem activeExponents_sum (i : Fin 3) : ∑ k, activeExponents i k = neighborLevel i := by
  fin_cases i <;> decide

theorem activeExponents_bound (i : Fin 3) (k : Fin 3) : activeExponents i k ≤ 1 := by
  unfold activeExponents
  split_ifs <;> omega

theorem activeElementaryModule_killed (q : ℕ) (i : Fin 3)
    (x : AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (activeExponents i)) : q • x = 0 := by
  simpa only [pow_one] using
    AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_killed q 1 (activeExponents i) (activeExponents_bound i) x

theorem neighborExponents_active {s : ℕ} (active : Fin s) (multiplicative : Fin s → Bool)
    (i : Fin 3) : neighborExponents active multiplicative i active = activeExponents i := by
  funext k
  simp [neighborExponents]

theorem neighborExponents_compact {s : ℕ} (active v : Fin s) (hv : v ≠ active)
    (multiplicative : Fin s → Bool) (i : Fin 3) :
    neighborExponents active multiplicative i v =
      fun _ => if multiplicative v then neighborLevel i else 0 := by
  funext k
  simp only [neighborExponents, ite_eq_right hv]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
