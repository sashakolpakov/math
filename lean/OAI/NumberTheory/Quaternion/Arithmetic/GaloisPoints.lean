import OAI.NumberTheory.Quaternion.Arithmetic.AlgebraicHypotheses
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois Points -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GaloisPoints

noncomputable section

/-! Galois action and descent for the actual matrix-group points.
Fixed points over a finite Galois extension come from rational points. -/

open scoped Classical
open _root_.Matrix

variable {F K : Type} [Field F] [Field K] [Algebra F K] {n : ℕ}

theorem galois_comp_algebraMap (σ : K ≃ₐ[F] K) :
    σ.toRingHom.comp (algebraMap F K) = algebraMap F K := by
  ext x
  exact σ.commutes x

def galoisPointsHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (σ : K ≃ₐ[F] K) :
    G.Points (algebraMap F K) →* G.Points (algebraMap F K) where
  toFun g := ⟨Matrix.SpecialLinearGroup.map σ.toRingHom g.val, by
    have h := (G.map (algebraMap F K) σ.toRingHom g).property
    change Matrix.SpecialLinearGroup.map σ.toRingHom g.val ∈
      G.subgroup K (σ.toRingHom.comp (algebraMap F K)) at h
    rw [galois_comp_algebraMap] at h
    exact h⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

theorem galoisPointsHom_entry (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (σ : K ≃ₐ[F] K)
    (g : G.Points (algebraMap F K)) (i j : Fin n) :
    (galoisPointsHom G σ g).val i j = σ (g.val i j) := rfl

theorem galoisPointsHom_one (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    galoisPointsHom G (1 : K ≃ₐ[F] K) = MonoidHom.id _ := by
  ext g i j
  exact galoisPointsHom_entry G 1 g i j

theorem galoisPointsHom_mul (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (σ τ : K ≃ₐ[F] K) :
    galoisPointsHom G (σ * τ) = (galoisPointsHom G σ).comp (galoisPointsHom G τ) := by
  ext g i j
  simp only [MonoidHom.comp_apply, galoisPointsHom_entry]
  rfl

theorem galois_fixed_matrix_descends [IsGalois F K] [FiniteDimensional F K]
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ σ : K ≃ₐ[F] K, A.map σ = A) :
    ∃ B : Matrix (Fin n) (Fin n) F, B.map (algebraMap F K) = A := by
  have he (i j : Fin n) : ∃ b : F, algebraMap F K b = A i j := by
    apply (IsGalois.mem_range_algebraMap_iff_fixed (A i j)).mpr
    intro σ
    exact congrFun (congrFun (hA σ) i) j
  choose B hB using he
  exact ⟨B, Matrix.ext hB⟩

theorem galois_fixed_point_descends [IsGalois F K] [FiniteDimensional F K]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : G.Points (algebraMap F K))
    (hg : ∀ σ : K ≃ₐ[F] K, galoisPointsHom G σ g = g) :
    ∃ a : G.RationalPoints, G.map (RingHom.id F) (algebraMap F K) a = g := by
  obtain ⟨B, hB⟩ := galois_fixed_matrix_descends (g.val : Matrix (Fin n) (Fin n) K) (by
    intro σ
    ext i j
    exact (galoisPointsHom_entry G σ g i j).symm.trans (congrArg (fun x => x.val i j) (hg σ)))
  have hdet : B.det = 1 := by
    apply (algebraMap F K).injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hB, g.val.property, map_one]
  let b : ArithmeticGroups.Lattices.Algebraic.SL n F := ⟨B, hdet⟩
  have hb : b ∈ G.subgroup F (RingHom.id F) := by
    apply (G.mem_iff F (RingHom.id F) b).mpr
    intro p hp
    apply (algebraMap F K).injective
    have hz := (G.mem_iff K (algebraMap F K) g.val).mp g.property p hp
    rw [map_zero]
    change (algebraMap F K) (MvPolynomial.eval₂Hom (RingHom.id F) (fun ij => B ij.1 ij.2) p) = 0
    rw [MvPolynomial.map_eval₂Hom]
    have he : (fun ij : Fin n × Fin n => algebraMap F K (B ij.1 ij.2)) =
        fun ij => g.val ij.1 ij.2 := funext fun ij => congrFun (congrFun hB ij.1) ij.2
    rw [he]
    exact hz
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun hB i) j

end

end OAI.NumberTheory.Quaternion.Arithmetic.GaloisPoints
