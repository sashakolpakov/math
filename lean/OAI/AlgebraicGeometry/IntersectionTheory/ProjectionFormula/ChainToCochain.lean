import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ComplexBounds
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Chain To Cochain -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChainToCochain

noncomputable section

/-! Native nonnegative chain complexes, including the finite free resolutions,
as cochain complexes in nonpositive degrees. Homology, finiteness, freeness,
and finite support are transported by the actual extension isomorphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R : Type) [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ)

def cochain : CochainComplex (ModuleCat.{0} R) ℤ := K.extend (ComplexShape.embeddingUpIntLE 0)

def termIso (n : ℕ) : (cochain R K).X (-(n : ℤ)) ≅ K.X n :=
  K.extendXIso (ComplexShape.embeddingUpIntLE 0) (by simp)

def homologyIso (n : ℕ) : (cochain R K).homology (-(n : ℤ)) ≅ K.homology n :=
  K.extendHomologyIso (ComplexShape.embeddingUpIntLE 0) (by simp)

theorem positive_zero (i : ℤ) (hi : 0 < i) : IsZero ((cochain R K).X i) :=
  K.isZero_extend_X (ComplexShape.embeddingUpIntLE 0) i
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).mpr hi)

theorem finite_terms (hK : ∀ n, Module.Finite R (K.X n)) (i : ℤ) :
    Module.Finite R ((cochain R K).X i) := by
  by_cases hi : 0 < i
  · let := ModuleCat.subsingleton_of_isZero (positive_zero R K i hi)
    infer_instance
  · have he : -(((-i).toNat : ℕ) : ℤ) = i := by omega
    rw [← he]
    let := hK (-i).toNat
    exact Module.Finite.equiv (termIso R K (-i).toNat).toLinearEquiv.symm

theorem free_terms (hK : ∀ n, Module.Free R (K.X n)) (i : ℤ) :
    Module.Free R ((cochain R K).X i) := by
  by_cases hi : 0 < i
  · let := ModuleCat.subsingleton_of_isZero (positive_zero R K i hi)
    infer_instance
  · have he : -(((-i).toNat : ℕ) : ℤ) = i := by omega
    rw [← he]
    let := hK (-i).toNat
    exact Module.Free.of_equiv (termIso R K (-i).toNat).toLinearEquiv.symm

theorem bounded (d : ℕ) (hK : ∀ n, d < n → IsZero (K.X n)) (i : ℤ)
    (hi : i < -(d : ℤ) ∨ 0 < i) : IsZero ((cochain R K).X i) := by
  rcases hi with hi | hi
  · have he : -(((-i).toNat : ℕ) : ℤ) = i := by omega
    rw [← he]
    exact (hK (-i).toNat (by omega)).of_iso (termIso R K (-i).toNat)
  · exact positive_zero R K i hi

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChainToCochain
