import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

/-! # Filtration Base Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength

noncomputable section

/-! A prime filtration computes the length after flat base change. The
identity is in ENat and requires no finiteness premise on those lengths. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

def length (M : ModuleCat.{u} R) : ℕ∞ := Module.length S (S ⊗[R] M)

omit [Module.Flat R S] in
theorem length_iso {M N : ModuleCat.{u} R} (e : M ≅ N) : FiltrationBaseLength.length R S M = FiltrationBaseLength.length R S N :=
  (((ProjectionFormula.Flat.Extension.baseChange R S).mapIso e).toLinearEquiv).length_eq

omit [Module.Flat R S] in
theorem length_zero (M : ModuleCat.{u} R) [Subsingleton M] : FiltrationBaseLength.length R S M = 0 :=
  Module.length_eq_zero

theorem length_shortExact (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact) :
    FiltrationBaseLength.length R S T.X₂ = FiltrationBaseLength.length R S T.X₁ + FiltrationBaseLength.length R S T.X₃ := by
  let F := ProjectionFormula.Flat.Extension.baseChange R S
  let : Mono T.f := hT.mono_f
  let : Epi T.g := hT.epi_g
  have h := hT.map F
  exact Module.length_eq_add_of_exact (T.map F).f.hom (T.map F).g.hom
    ((ModuleCat.mono_iff_injective _).mp h.mono_f)
    ((ModuleCat.epi_iff_surjective _).mp h.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact)

theorem submodule_step (M : ModuleCat.{u} R) (L K : Submodule R M) (hLK : L ≤ K) :
    FiltrationBaseLength.length R S (.of R K) = FiltrationBaseLength.length R S (.of R L) +
      FiltrationBaseLength.length R S (.of R (K ⧸ L.submoduleOf K)) := by
  have h := length_shortExact R S (IsolatedTorEuler.submoduleSequence R (.of R K) (L.submoduleOf K))
    (IsolatedTorEuler.submoduleSequence_shortExact R (.of R K) (L.submoduleOf K))
  change FiltrationBaseLength.length R S (.of R K) = FiltrationBaseLength.length R S (.of R (L.submoduleOf K)) +
    FiltrationBaseLength.length R S (.of R (K ⧸ L.submoduleOf K)) at h
  rw [length_iso R S (Submodule.submoduleOfEquivOfLe hLK).toModuleIso] at h
  exact h

theorem filtration_sum (M : ModuleCat.{u} R)
    (s : RelSeries {(L, K) | Submodule.IsQuotientEquivQuotientPrime (A := R) (M := M) L K})
    (h₀ : s.head = ⊥) (ht : s.last = ⊤) :
    FiltrationBaseLength.length R S M = ∑ i : Fin s.length,
      FiltrationBaseLength.length R S (.of R (s i.succ ⧸ (s i.castSucc).submoduleOf (s i.succ))) := by
  have hs (n : ℕ) (hn : n < s.length + 1) :
      FiltrationBaseLength.length R S (.of R (s ⟨n, hn⟩)) = ∑ i : Fin n,
        FiltrationBaseLength.length R S (.of R (s ⟨i.val + 1, (Nat.succ_le_of_lt i.isLt).trans_lt hn⟩ ⧸
          (s ⟨i.val, i.isLt.trans hn⟩).submoduleOf
            (s ⟨i.val + 1, (Nat.succ_le_of_lt i.isLt).trans_lt hn⟩))) := by
    induction n with
    | zero =>
      change FiltrationBaseLength.length R S (.of R s.head) = _
      rw [h₀, length_zero]
      simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      rw [submodule_step R S M (s ⟨n, by omega⟩) (s ⟨n + 1, hn⟩) (s.step ⟨n, by omega⟩).1,
        ih (by omega)]
      rfl
  have h := hs s.length (by omega)
  change FiltrationBaseLength.length R S (.of R s.last) = _ at h
  rw [ht, length_iso R S (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).toModuleIso] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength
