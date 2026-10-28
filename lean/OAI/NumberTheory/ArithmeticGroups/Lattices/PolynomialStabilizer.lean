import OAI.NumberTheory.ArithmeticGroups.Lattices.VanishingIdeal

/-! # Polynomial Stabilizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialStabilizer.Construction

noncomputable section

/-! A finite-dimensional polynomial subspace detecting membership in the
matrix group. This is the subspace stage of the stabilizer construction. -/

open scoped Classical
open _root_.MvPolynomial

def boundedVanishingSpace {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ) : Submodule k (Algebraic.CoordinatePolynomial n k) :=
  (VanishingIdeal.Construction.coordinateVanishingIdeal G).restrictScalars k ⊓
    restrictTotalDegree (Fin n × Fin n) k d

theorem boundedVanishingSpace_fg {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ) : (boundedVanishingSpace G d).FG :=
  (Submodule.FG.of_finite (N := restrictTotalDegree (Fin n × Fin n) k d)).of_le inf_le_right

theorem rightTranslate_mem_boundedVanishingSpace {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ)
    (g : Algebraic.SL n k) (hg : g ∈ G.subgroup k (RingHom.id k))
    (p : Algebraic.CoordinatePolynomial n k) (hp : p ∈ boundedVanishingSpace G d) :
    PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p ∈ boundedVanishingSpace G d := by
  refine ⟨VanishingIdeal.Construction.rightTranslate_mem_vanishingIdeal G g hg p hp.1, ?_⟩
  apply (mem_restrictTotalDegree _ _ _).mpr
  exact (PolynomialAction.Construction.rightTranslate_totalDegree_le _ p).trans ((mem_restrictTotalDegree _ _ _).mp hp.2)

theorem rightTranslate_boundedVanishingSpace_eq {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ)
    (g : Algebraic.SL n k) (hg : g ∈ G.subgroup k (RingHom.id k)) :
    (boundedVanishingSpace G d).map
      (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap =
      boundedVanishingSpace G d := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact rightTranslate_mem_boundedVanishingSpace G d g hg p hp
  · intro p hp
    refine ⟨PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p,
      rightTranslate_mem_boundedVanishingSpace G d g⁻¹
        ((G.subgroup k (RingHom.id k)).inv_mem hg) p hp, ?_⟩
    exact (PolynomialAction.Construction.rightTranslateEquiv g).apply_symm_apply p

theorem exists_bounded_polynomial_stabilizer {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) :
    ∃ d : ℕ, ∀ g : Algebraic.SL n k,
      g ∈ G.subgroup k (RingHom.id k) ↔
        (boundedVanishingSpace G d).map
          (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap =
          boundedVanishingSpace G d := by
  obtain ⟨S, hS, hdef⟩ := VanishingIdeal.Construction.exists_finite_defining_polynomials G
  let d : ℕ := S.sup MvPolynomial.totalDegree
  refine ⟨d, fun g => ⟨rightTranslate_boundedVanishingSpace_eq G d g, ?_⟩⟩
  intro hstable
  apply (hdef k (RingHom.id k) g).mpr
  intro p hp
  have hpI : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := hS ▸ Ideal.subset_span hp
  have hpD : p ∈ restrictTotalDegree (Fin n × Fin n) k d :=
    (mem_restrictTotalDegree _ _ _).mpr (Finset.le_sup hp)
  have htrans : PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p ∈
      boundedVanishingSpace G d := by
    rw [← hstable]
    exact ⟨p, ⟨hpI, hpD⟩, rfl⟩
  have hzero := htrans.1 k (RingHom.id k)
    (1 : G.Points (RingHom.id k))
  rw [PolynomialAction.Construction.rightTranslate_evaluate] at hzero
  have hid : Matrix.SpecialLinearGroup.map (RingHom.id k) g = g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  simpa only [OneMemClass.coe_one, one_mul, hid] using hzero

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialStabilizer.Construction
