import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Acyclic Side Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.AcyclicSideComparison

noncomputable section

/-! In a short exact sequence of nonnegative cochain complexes, an acyclic end term makes the opposite structure map a quasi-isomorphism, including degree zero. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
universe u v
variable {V : Type u} [Category.{v} V] [Abelian V]
    {S : ShortComplex (CochainComplex V ℕ)}

theorem cochain_quasiIso_f_of_acyclic_last (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) :
    QuasiIso S.f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Epi (homologyMap S.f n) :=
    (hS.homology_exact₂ n).epi_f ((h₃ n).isZero_homology.eq_of_tgt _ _)
  have : Mono (homologyMap S.f n) := by
    cases n with
    | zero =>
        have : Mono S.f := hS.mono_f
        exact mono_homologyMap_of_mono_of_not_rel S.f 0 (by
          intro i hi
          change i + 1 = 0 at hi
          omega)
    | succ n =>
        exact (hS.homology_exact₁ n (n + 1) (by simp)).mono_g
          ((h₃ n).isZero_homology.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

theorem cochain_quasiIso_g_of_acyclic_first (hS : S.ShortExact) (h₁ : S.X₁.Acyclic) :
    QuasiIso S.g := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g ((h₁ n).isZero_homology.eq_of_src _ _)
  have : Epi (homologyMap S.g n) :=
    (hS.homology_exact₃ n (n + 1) (by simp)).epi_f
      ((h₁ (n + 1)).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.AcyclicSideComparison
