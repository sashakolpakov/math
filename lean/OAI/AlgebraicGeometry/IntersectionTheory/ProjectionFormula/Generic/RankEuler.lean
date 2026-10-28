import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! # Rank Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.RankEuler

noncomputable section

/-! A flat extension to a field computes the alternating ranks of a
finite free resolution. Thus finite-length Tor Euler characteristics are
length times generic rank, and vanish when that rank vanishes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R K : Type u) [CommRing R] [Nontrivial R] [Field K] [Algebra R K] [Module.Flat R K]

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

theorem alternating_rank (N : ModuleCat.{u} R) [Module.Finite R N]
    (P : ProjectiveResolution N)
    (hP : ∀ n, Module.Finite R (P.complex.X n) ∧ Module.Free R (P.complex.X n))
    (d : ℕ) (hd : IsZero (P.complex.X (d + 1))) :
    (∑ n ∈ Finset.range (d + 1), (-1 : ℚ) ^ n * (Module.finrank R (P.complex.X n) : ℚ)) =
      (Module.finrank K (K ⊗[R] N) : ℚ) := by
  let Q := (ProjectionFormula.Flat.Extension.baseChange R K).mapProjectiveResolution P
  have hfin (n : ℕ) : Module.Finite K (Q.complex.X n) := by
    let := (hP n).1
    change Module.Finite K (K ⊗[R] P.complex.X n)
    infer_instance
  have hlen (n : ℕ) : Module.length K (Q.complex.X n) ≠ ⊤ := by
    let := hfin n
    exact Module.length_ne_top
  have hdQ : IsZero (Q.complex.X (d + 1)) := (ProjectionFormula.Flat.Extension.baseChange R K).map_isZero hd
  have h := ResolutionEuler.resolution_length K ((ProjectionFormula.Flat.Extension.baseChange R K).obj N) Q hlen d hdQ
  have he (n : ℕ) : ExactLength.rationalLength K (Q.complex.X n) = (Module.finrank R (P.complex.X n) : ℚ) := by
    let := (hP n).1
    let := (hP n).2
    change ((Module.length K (K ⊗[R] P.complex.X n)).toNat : ℚ) = _
    rw [Module.length_eq_finrank, ENat.toNat_natCast, Module.finrank_baseChange]
  have hn : ExactLength.rationalLength K ((ProjectionFormula.Flat.Extension.baseChange R K).obj N) = (Module.finrank K (K ⊗[R] N) : ℚ) := by
    change ((Module.length K (K ⊗[R] N)).toNat : ℚ) = _
    rw [Module.length_eq_finrank, ENat.toNat_natCast]
  simpa only [he, hn] using h.symm

omit [Nontrivial R] in
theorem finite_length_euler [IsNoetherianRing R] [IsLocalRing R]
    (M N : ModuleCat.{u} R) (hM : Module.length R M ≠ ⊤) [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d] :
    Tor.Euler.euler R M N d = ExactLength.rationalLength R M * (Module.finrank K (K ⊗[R] N) : ℚ) := by
  obtain ⟨P, hP, hd⟩ := ProjectionFormula.Finite.BoundedResolution.exists_finite_free_bounded_resolution R N d
  rw [ResolutionEuler.tor_euler_rank_sum R M N hM P hP d (hd _ (by omega)),
    alternating_rank R K N P hP d (hd _ (by omega))]

omit [Nontrivial R] in
theorem finite_length_euler_zero [IsNoetherianRing R] [IsLocalRing R]
    (M N : ModuleCat.{u} R) (hM : Module.length R M ≠ ⊤) [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d] [Subsingleton (K ⊗[R] N)] :
    Tor.Euler.euler R M N d = 0 := by
  rw [finite_length_euler R K M N hM d]
  rw [Module.finrank_zero_of_subsingleton]
  simp

omit [Nontrivial R] [Field K] [Algebra R K] [Module.Flat R K] in
theorem finite_length_torsion_euler_zero [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (M N : ModuleCat.{u} R) (hM : Module.length R M ≠ ⊤) [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d]
    (hN : ∀ x : N, ∃ r : R, r ≠ 0 ∧ r • x = 0) : Tor.Euler.euler R M N d = 0 := by
  let : Subsingleton (LocalizedModule (nonZeroDivisors R) N) :=
    LocalizedModule.subsingleton_iff.mpr (fun x => by
      obtain ⟨r, hr, hx⟩ := hN x
      exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, hx⟩)
  let : Subsingleton (FractionRing R ⊗[R] N) :=
    (LocalizedModule.equivTensorProduct (nonZeroDivisors R) N).symm.injective.subsingleton
  exact finite_length_euler_zero R (FractionRing R) M N hM d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.RankEuler
