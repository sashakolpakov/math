import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicFrame

/-! # Logarithmic Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicHomotopy.Forms

noncomputable section

/-! A canonical finite primitive for changing logarithmic coordinate
lifts. Fixing the truncation length removes all choices from the local
boundary representative. -/
open _root_.CategoryTheory
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def primitiveOne (N : ℕ) (u v : Aˣ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 0 :=
  LogarithmicForms.zeroForm R A I δ (Logarithm.logarithm I δ N ((↑(v * u⁻¹) : A) - 1))

theorem ratio_mem (u v : Aˣ) (huv : (v : A) - (u : A) ∈ I) :
    (↑(v * u⁻¹) : A) - 1 ∈ I := by
  have he : (↑(v * u⁻¹) : A) - 1 = ((v : A) - (u : A)) * ↑u⁻¹ := by
    rw [Units.val_mul, sub_mul, Units.mul_inv]
  rw [he]
  exact I.mul_mem_right _ huv

theorem primitiveOne_differential (N : ℕ) (hN : (N.factorial : A) = 0)
    (u v : Aˣ) (huv : (v : A) - (u : A) ∈ I) :
    LogarithmicForms.dlog R A I δ v - LogarithmicForms.dlog R A I δ u =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 0 (primitiveOne R A I δ N u v) := by
  rw [primitiveOne, LogarithmicForms.differential_zeroForm]
  have hx := ratio_mem A I u v huv
  exact Logarithm.dlog_sub_exact I δ (AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R A I δ) N u v hx hN
    (fun j => AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D_dpow R A I δ j hx)

def logarithmicPrimitive (N : ℕ) : (n : ℕ) →
    (Fin (n + 1) → Aˣ) → (Fin (n + 1) → Aˣ) → AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n
  | 0, u, v => primitiveOne R A I δ N (u 0) (v 0)
  | n + 1, u, v =>
      DeRhamWedge.wedge R A I δ n 1
          (logarithmicPrimitive N n (fun i => u i.castSucc) (fun i => v i.castSucc))
          (LogarithmicForms.dlog R A I δ (v (Fin.last (n + 1)))) +
        (-1 : ℤ) ^ (n + 1) • DeRhamWedge.wedge R A I δ (n + 1) 0
          (LogarithmicWedges.Forms.logarithmicWedge R A I δ (n + 1) (fun i => u i.castSucc))
          (primitiveOne R A I δ N (u (Fin.last (n + 1))) (v (Fin.last (n + 1))))

theorem logarithmicPrimitive_differential (N : ℕ) (hN : (N.factorial : A) = 0)
    (n : ℕ) (u v : Fin (n + 1) → Aˣ)
    (huv : ∀ i, (v i : A) - (u i : A) ∈ I) :
    LogarithmicWedges.Forms.logarithmicWedge R A I δ (n + 1) v - LogarithmicWedges.Forms.logarithmicWedge R A I δ (n + 1) u =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n (Forms.logarithmicPrimitive R A I δ N n u v) := by
  induction n with
  | zero =>
      rw [LogarithmicWedges.Forms.logarithmicWedge_one, LogarithmicWedges.Forms.logarithmicWedge_one]
      exact primitiveOne_differential R A I δ N hN (u 0) (v 0) (huv 0)
  | succ n ih =>
      have hη := ih (fun i => u i.castSucc) (fun i => v i.castSucc)
        (fun i => huv i.castSucc)
      have hξ := primitiveOne_differential R A I δ N hN
        (u (Fin.last (n + 1))) (v (Fin.last (n + 1))) (huv (Fin.last (n + 1)))
      have hs : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by
        rw [← mul_pow]
        simp
      rw [Forms.logarithmicPrimitive, map_add, map_zsmul,
        LogarithmicWedges.Forms.differential_wedge_closed_one R A I δ _ _ _ (LogarithmicForms.dlog_closed R A I δ _),
        LogarithmicWedges.Forms.differential_closed_wedge_zero R A I δ _ _ (LogarithmicWedges.Forms.logarithmicWedge_closed R A I δ _ _) _,
        smul_smul, hs, one_smul, ← hη, ← hξ]
      simp only [LogarithmicWedges.Forms.logarithmicWedge, map_sub, LinearMap.sub_apply]
      abel

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicHomotopy.Forms
