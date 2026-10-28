import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-! # Double Complex Rows -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRows.DoubleComplex

/-! Concrete row exactness and augmentation lemmas for genuine first-quadrant bicomplexes. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [Ring R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- Exactness of a positive horizontal row term is the usual kernel/image condition. -/
theorem row_exact_iff (p q : ℕ) :
    (K.flip.X q).ExactAt (p + 1) ↔
      Function.Exact ((K.d p (p + 1)).f q) ((K.d (p + 1) (p + 2)).f q) := by
  rw [HomologicalComplex.exactAt_iff' _ p (p + 1) (p + 2) (by simp) (by simp)]
  exact ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _

/-- A horizontal cycle in a positive Čech degree has a predecessor in an exact row. -/
theorem row_primitive (p q : ℕ) (hexact : (K.flip.X q).ExactAt (p + 1))
    (x : (K.X (p + 1)).X q) (hx : ((K.d (p + 1) (p + 2)).f q) x = 0) :
    ∃ y : (K.X p).X q, ((K.d p (p + 1)).f q) y = x :=
  ((row_exact_iff K p q).mp hexact x).mp hx

variable {K} {A : CochainComplex (ModuleCat.{v} R) ℕ} (ε : A ⟶ K.X 0)

/-- An injective augmentation reflects closedness using its actual cochain-map law. -/
theorem augmentation_reflects_closed (n : ℕ) (hinj : Function.Injective (ε.f (n + 1)))
    (a : A.X n) (ha : (K.X 0).d n (n + 1) (ε.f n a) = 0) :
    A.d n (n + 1) a = 0 := by
  apply hinj
  rw [map_zero]
  have h := congrArg (fun f : A.X n ⟶ (K.X 0).X (n + 1) => f a) (ε.comm n (n + 1))
  exact h.symm.trans ha

/-- At an exact augmented row, a boundary in the zero column lifts to a
boundary in the augmenting complex. -/
theorem augmentation_lifts_boundary (n : ℕ)
    (hinj : Function.Injective (ε.f (n + 1)))
    (hexact : Function.Exact (ε.f n) ((K.d 0 1).f n))
    (a : A.X (n + 1)) (b : (K.X 0).X n)
    (hb : ((K.d 0 1).f n) b = 0)
    (ha : ε.f (n + 1) a = (K.X 0).d n (n + 1) b) :
    ∃ c : A.X n, A.d n (n + 1) c = a := by
  obtain ⟨c, hc⟩ := (hexact b).mp hb
  refine ⟨c, hinj ?_⟩
  have h := congrArg (fun f : A.X n ⟶ (K.X 0).X (n + 1) => f c) (ε.comm n (n + 1))
  calc
    ε.f (n + 1) (A.d n (n + 1) c) = (K.X 0).d n (n + 1) (ε.f n c) := h.symm
    _ = (K.X 0).d n (n + 1) b := congrArg ((K.X 0).d n (n + 1)) hc
    _ = ε.f (n + 1) a := ha.symm

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexRows.DoubleComplex
