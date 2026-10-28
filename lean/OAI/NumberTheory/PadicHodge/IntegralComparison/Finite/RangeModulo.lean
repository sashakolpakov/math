import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Range Modulo -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.RangeModulo

noncomputable section

/-! Finite generation of an image detected modulo a finite submodule. -/

universe u v w z

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type z} [AddCommGroup P] [Module R P]

theorem finite_range (f : M →ₗ[R] N) (g : M →ₗ[R] P) (S : Submodule R N)
    [Module.Finite R P] [Module.Finite R S]
    (h : ∀ x, g x = 0 → f x ∈ S) : Module.Finite R f.range := by
  let q := S.mkQ
  have hker : g.ker ≤ (q.comp f).ker := by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero S).mpr (h x hx)
  let l := g.ker.liftQ (q.comp f) hker
  let : Module.Finite R (M ⧸ g.ker) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  have hcomp : l.comp g.ker.mkQ = q.comp f := by ext; rfl
  have hmap : (f.range.map q).FG := by
    rw [← LinearMap.range_comp, ← hcomp, LinearMap.range_comp,
      Submodule.range_mkQ, Submodule.map_top]
    exact Submodule.fg_range l
  have hinf : (f.range ⊓ q.ker).FG := by
    have hle : f.range ⊓ q.ker ≤ S := by
      simpa only [q, Submodule.ker_mkQ] using (inf_le_right : f.range ⊓ S ≤ S)
    exact Submodule.FG.of_le_of_isNoetherian hle
  exact ⟨(Submodule.fg_top f.range).mpr (Submodule.fg_of_fg_map_of_fg_inf_ker q hmap hinf)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.RangeModulo
