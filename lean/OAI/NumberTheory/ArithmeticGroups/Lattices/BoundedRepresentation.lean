import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialStabilizer

/-! # Bounded Representation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedRepresentation.Construction

noncomputable section

/-! The finite-dimensional representation on polynomials of bounded degree. -/

open scoped Classical
open _root_.MvPolynomial

abbrev BoundedPolynomials (k : Type) [Field k] (n d : ℕ) :=
  restrictTotalDegree (Fin n × Fin n) k d

def boundedPolynomialEquiv {k : Type} [Field k] {n : ℕ}
    (d : ℕ) (g : Algebraic.SL n k) : BoundedPolynomials k n d ≃ₗ[k] BoundedPolynomials k n d where
  toFun p := ⟨PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p.val,
    (mem_restrictTotalDegree _ _ _).mpr
      ((PolynomialAction.Construction.rightTranslate_totalDegree_le _ p.val).trans
        ((mem_restrictTotalDegree _ _ _).mp p.property))⟩
  invFun p := ⟨PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p.val,
    (mem_restrictTotalDegree _ _ _).mpr
      ((PolynomialAction.Construction.rightTranslate_totalDegree_le _ p.val).trans
        ((mem_restrictTotalDegree _ _ _).mp p.property))⟩
  left_inv p := Subtype.ext (PolynomialAction.Construction.rightTranslate_inverse_left g p.val)
  right_inv p := Subtype.ext ((PolynomialAction.Construction.rightTranslateEquiv g).apply_symm_apply p.val)
  map_add' p q := Subtype.ext (map_add _ p.val q.val)
  map_smul' c p := Subtype.ext
    ((PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap.map_smul c p.val)

def boundedPolynomialRepresentation {k : Type} [Field k] {n : ℕ} (d : ℕ) :
    Algebraic.SL n k →* (BoundedPolynomials k n d ≃ₗ[k] BoundedPolynomials k n d) where
  toFun := boundedPolynomialEquiv d
  map_one' := by
    apply LinearEquiv.ext
    intro p
    apply Subtype.ext
    change PolynomialAction.Construction.rightTranslate (1 : Matrix (Fin n) (Fin n) k) p.val = p.val
    rw [PolynomialAction.Construction.rightTranslate_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro p
    apply Subtype.ext
    change PolynomialAction.Construction.rightTranslate ((g * h : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p.val =
      PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)
        (PolynomialAction.Construction.rightTranslate (h : Matrix (Fin n) (Fin n) k) p.val)
    rw [Matrix.SpecialLinearGroup.coe_mul, PolynomialAction.Construction.rightTranslate_mul]
    rfl

def boundedIdealSubspace {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ) : Submodule k (BoundedPolynomials k n d) :=
  ((VanishingIdeal.Construction.coordinateVanishingIdeal G).restrictScalars k).comap
    (restrictTotalDegree (Fin n × Fin n) k d).subtype

theorem mem_boundedIdealSubspace {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ) (p : BoundedPolynomials k n d) :
    p ∈ boundedIdealSubspace G d ↔ p.val ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := Iff.rfl

theorem boundedIdealSubspace_map_subtype {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ) :
    (boundedIdealSubspace G d).map (BoundedPolynomials k n d).subtype =
      PolynomialStabilizer.Construction.boundedVanishingSpace G d := by
  simp [boundedIdealSubspace, PolynomialStabilizer.Construction.boundedVanishingSpace, BoundedPolynomials,
    Submodule.map_comap_subtype, inf_comm]

theorem boundedIdealSubspace_stabilizer_iff {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ) (g : Algebraic.SL n k) :
    (boundedIdealSubspace G d).map (boundedPolynomialRepresentation d g).toLinearMap =
      boundedIdealSubspace G d ↔
    (PolynomialStabilizer.Construction.boundedVanishingSpace G d).map
      (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap =
      PolynomialStabilizer.Construction.boundedVanishingSpace G d := by
  have hcomp : (BoundedPolynomials k n d).subtype.comp
      (boundedPolynomialRepresentation d g).toLinearMap =
      (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)).toLinearMap.comp
        (BoundedPolynomials k n d).subtype := by
    apply LinearMap.ext
    intro p
    rfl
  rw [← (Submodule.map_injective_of_injective
    (show Function.Injective (BoundedPolynomials k n d).subtype from Subtype.val_injective)).eq_iff]
  rw [← Submodule.map_comp, hcomp, Submodule.map_comp, boundedIdealSubspace_map_subtype]

theorem exists_finite_dimensional_stabilizer {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) :
    ∃ d : ℕ, ∀ g : Algebraic.SL n k,
      g ∈ G.subgroup k (RingHom.id k) ↔
        (boundedIdealSubspace G d).map (boundedPolynomialRepresentation d g).toLinearMap =
          boundedIdealSubspace G d := by
  obtain ⟨d, hd⟩ := PolynomialStabilizer.Construction.exists_bounded_polynomial_stabilizer G
  exact ⟨d, fun g => (hd g).trans (boundedIdealSubspace_stabilizer_iff G d g).symm⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedRepresentation.Construction
