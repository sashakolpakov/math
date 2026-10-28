import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Kill Variables -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.KillVariables.GradedHilbert

noncomputable section

/-! Setting complementary polynomial variables to zero: kernel, surjectivity, and homogeneity. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type v} {τ : Type w} {R : Type u} [CommRing R]
variable {f : σ → τ} (hf : Function.Injective f)

theorem killVariables_surjective : Function.Surjective (MvPolynomial.killCompl (R := R) hf) :=
  fun p => ⟨rename f p, killCompl_rename_app hf p⟩

theorem killVariables_kernel :
    RingHom.ker (MvPolynomial.killCompl (R := R) hf).toRingHom =
      Ideal.span (MvPolynomial.X '' (Set.range f)ᶜ) := by
  classical
  apply Ideal.ext
  intro p
  rw [RingHom.mem_ker, mem_ideal_span_X_image]
  constructor
  · intro hp m hm
    change MvPolynomial.killCompl hf p = 0 at hp
    by_contra! h
    have hs : (m.support : Set τ) ⊆ Set.range f := by
      intro i hi
      by_contra hi'
      exact (Finsupp.mem_support_iff.mp hi) (h i hi')
    have hc := congrArg ((fun p => AddMonoidAlgebra.coeff p ((m.comapDomain f hf.injOn)))) hp
    rw [coeff_killCompl, AddMonoidAlgebra.coeff_zero, Finsupp.mapDomain_comapDomain f hf m hs] at hc
    exact (mem_support_iff.mp hm) hc
  · intro hp
    apply MvPolynomial.ext
    intro a
    change AddMonoidAlgebra.coeff ((MvPolynomial.killCompl hf p)) (a) = AddMonoidAlgebra.coeff (0) (a)
    rw [coeff_killCompl, AddMonoidAlgebra.coeff_zero]
    by_contra ha
    obtain ⟨i, hi, hia⟩ := hp (a.mapDomain f) (mem_support_iff.mpr ha)
    exact hia (Finsupp.mapDomain_of_notMem_range a i hi)

theorem killVariables_homogeneous {p : MvPolynomial τ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (MvPolynomial.killCompl hf p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain f) ≠ 0 := by rwa [coeff_killCompl] at ha
  have hd := hp hcoeff
  have ha' := DFunLike.congr_fun (Finsupp.degree_eq_weight_one (R := ℕ) (σ := σ)) a
  have hm := DFunLike.congr_fun (Finsupp.degree_eq_weight_one (R := ℕ) (σ := τ)) (a.mapDomain f)
  exact ha'.symm.trans ((Finsupp.degree_mapDomain f a).symm.trans (hm.trans hd))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.KillVariables.GradedHilbert
