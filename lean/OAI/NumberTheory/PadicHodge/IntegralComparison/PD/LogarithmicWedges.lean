import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedgeAlgebra

/-! # Logarithmic Wedges -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicWedges.Forms

noncomputable section

/-! Products of native logarithmic PD forms are closed, and changing
each unit by an element of the PD ideal changes the product by a
boundary in the original PD de Rham complex. -/
open OAI.NumberTheory.PadicHodge.IntegralComparison.PD.DeRhamWedgeAlgebra
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def logarithmicWedge : (n : ℕ) → (Fin n → Aˣ) → AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n
  | 0, _ => DeRhamWedgeAlgebra.unitForm R A I δ
  | n + 1, v => DeRhamWedge.wedge R A I δ n 1
      (logarithmicWedge n (fun i => v i.castSucc)) (LogarithmicForms.dlog R A I δ (v (Fin.last n)))

theorem logarithmicWedge_one (v : Fin 1 → Aˣ) :
    Forms.logarithmicWedge R A I δ 1 v = LogarithmicForms.dlog R A I δ (v 0) := by
  simpa only [DeRhamLeibniz.Wedge.degreeCast, Forms.logarithmicWedge, LinearEquiv.refl_apply, Fin.last_zero] using
    (DeRhamWedgeAlgebra.unit_wedge R A I δ (LogarithmicForms.dlog R A I δ (v 0)))

theorem logarithmicWedge_closed (n : ℕ) (v : Fin n → Aˣ) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n (Forms.logarithmicWedge R A I δ n v) = 0 := by
  induction n with
  | zero => exact DeRhamWedgeAlgebra.differential_unit R A I δ
  | succ n ih =>
      rw [Forms.logarithmicWedge, DeRhamLeibniz.Wedge.differential_wedge, ih, LogarithmicForms.dlog_closed]
      simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]

theorem differential_wedge_closed_one (n : ℕ) (η : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n)
    (y : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 1) (hy : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 1 y = 0) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ (n + 1) (DeRhamWedge.wedge R A I δ n 1 η y) =
      DeRhamWedge.wedge R A I δ (n + 1) 1 (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n η) y := by
  rw [DeRhamLeibniz.Wedge.differential_wedge, hy, map_zero, map_zero, smul_zero, add_zero]
  rfl

theorem differential_closed_wedge_zero (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n)
    (hx : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n x = 0) (η : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ 0) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n (DeRhamWedge.wedge R A I δ n 0 x η) =
      (-1 : ℤ) ^ n • DeRhamWedge.wedge R A I δ n 1 x (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 0 η) := by
  have h := DeRhamLeibniz.Wedge.differential_wedge R A I δ n 0 x η
  simpa only [hx, map_zero, LinearMap.zero_apply, zero_add, DeRhamLeibniz.Wedge.degreeCast,
    LinearEquiv.refl_apply, Nat.add_zero] using h

theorem congruent_wedges_exact (p r : ℕ) (hp : 0 < p) (hpr : (p : A) ^ r = 0)
    (n : ℕ) (u v : Fin (n + 1) → Aˣ)
    (huv : ∀ i, (v i : A) - (u i : A) ∈ I) :
    ∃ η : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R A I δ n,
      Forms.logarithmicWedge R A I δ (n + 1) v - Forms.logarithmicWedge R A I δ (n + 1) u =
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ n η := by
  induction n with
  | zero =>
      rw [logarithmicWedge_one, logarithmicWedge_one]
      exact LogarithmicForms.congruent_units_exact R A I δ p r hp hpr (u 0) (v 0) (huv 0)
  | succ n ih =>
      obtain ⟨η, hη⟩ := ih (fun i => u i.castSucc) (fun i => v i.castSucc)
        (fun i => huv i.castSucc)
      obtain ⟨ξ, hξ⟩ := LogarithmicForms.congruent_units_exact R A I δ p r hp hpr
        (u (Fin.last (n + 1))) (v (Fin.last (n + 1))) (huv (Fin.last (n + 1)))
      let x := Forms.logarithmicWedge R A I δ (n + 1) (fun i => u i.castSucc)
      let y := LogarithmicForms.dlog R A I δ (v (Fin.last (n + 1)))
      refine ⟨DeRhamWedge.wedge R A I δ n 1 η y +
        (-1 : ℤ) ^ (n + 1) • DeRhamWedge.wedge R A I δ (n + 1) 0 x ξ, ?_⟩
      have hx : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ (n + 1) x = 0 :=
        logarithmicWedge_closed R A I δ _ _
      have hy : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R A I δ 1 y = 0 := LogarithmicForms.dlog_closed R A I δ _
      have hs : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 := by
        rw [← mul_pow]
        simp
      rw [map_add, map_zsmul, differential_wedge_closed_one R A I δ n η y hy,
        differential_closed_wedge_zero R A I δ (n + 1) x hx ξ,
        smul_smul, hs, one_smul, ← hη, ← hξ]
      simp only [Forms.logarithmicWedge, x, y, map_sub, LinearMap.sub_apply]
      abel

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicWedges.Forms
