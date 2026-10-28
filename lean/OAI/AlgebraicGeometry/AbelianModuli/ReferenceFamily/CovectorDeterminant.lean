import OAI.AlgebraicTopology.Kunneth.CovectorWedge

/-! # Covector Determinant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CovectorDeterminant

noncomputable section

/-! The normalization of the original exterior product in degree (1,1). -/

open OAI.AlgebraicTopology.Kunneth.CovectorWedge.Constructions
open scoped BigOperators

theorem permFinTwo_univ : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
    {1, Equiv.swap 0 1} := by
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  by_cases h : σ 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h
    · change σ 1 = 1
      have hn : σ 1 ≠ 0 := fun hn => (by decide : (1 : Fin 2) ≠ 0) (σ.injective (hn.trans h.symm))
      omega
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · have he : σ 0 = 1 := by omega
      simpa using he
    · have he : σ 0 = 1 := by omega
      have hn : σ 1 ≠ 1 := fun hn => (by decide : (1 : Fin 2) ≠ 0) (σ.injective (hn.trans he.symm))
      have hz : σ 1 = 0 := by omega
      simpa using hz

theorem covectorWedge_one_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E [⋀^Fin 1]→L[ℝ] ℂ) (u v : E) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b ![u, v] =
      a (fun _ => u) * b (fun _ => v) - a (fun _ => v) * b (fun _ => u) := by
  rw [AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_apply]
  have hn : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have he := DFunLike.congr_fun h 0
    norm_num at he
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, inv_one, one_smul]
  rw [permFinTwo_univ, Finset.sum_pair hn]
  have h0 : (fun i : Fin 1 => ![u, v] ((1 : Equiv.Perm (Fin 2)) (Fin.castAdd 1 i))) = fun _ => u := by
    funext i; fin_cases i; rfl
  have h1 : (fun i : Fin 1 => ![u, v] ((1 : Equiv.Perm (Fin 2)) (Fin.natAdd 1 i))) = fun _ => v := by
    funext i; fin_cases i; rfl
  have h2 : (fun i : Fin 1 => ![u, v] ((Equiv.swap 0 1) (Fin.castAdd 1 i))) = fun _ => v := by
    funext i; fin_cases i; simp
  have h3 : (fun i : Fin 1 => ![u, v] ((Equiv.swap 0 1) (Fin.natAdd 1 i))) = fun _ => u := by
    funext i; fin_cases i; simp
  rw [h0, h1, h2, h3]
  simp [sub_eq_add_neg]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CovectorDeterminant
