import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Cokernel Syzygy Sequence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CokernelSyzygySequence

noncomputable section

/-! Adjacent cokernels in an exact sequence give a short exact sequence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L M N : C} (f : L ⟶ M) (g : M ⟶ N) (hfg : f ≫ g = 0)

def cokernelSyzygyShortComplex : ShortComplex C :=
  ShortComplex.mk (cokernel.desc f g hfg) (cokernel.π g) (by
    apply (cancel_epi (cokernel.π f)).mp
    rw [← Category.assoc, cokernel.π_desc, cokernel.condition, comp_zero])

theorem cokernelSyzygyShortComplex_shortExact (hex : (ShortComplex.mk f g hfg).Exact) :
    (cokernelSyzygyShortComplex f g hfg).ShortExact := by
  let S := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  let T := cokernelSyzygyShortComplex f g hfg
  let φ : S ⟶ T :=
    { τ₁ := cokernel.π f, τ₂ := 𝟙 N, τ₃ := 𝟙 (cokernel g)
      comm₁₂ := by simp [S, T, cokernelSyzygyShortComplex]
      comm₂₃ := by simp [S, T, cokernelSyzygyShortComplex] }
  have : Epi φ.τ₁ := by dsimp only [φ, S, T, cokernelSyzygyShortComplex]; infer_instance
  have : IsIso φ.τ₂ := by dsimp only [φ, S, T, cokernelSyzygyShortComplex]; infer_instance
  have : Mono φ.τ₃ := by dsimp only [φ, S, T, cokernelSyzygyShortComplex]; infer_instance
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
    (ShortComplex.cokernelSequence_exact g)
  have : Mono T.f := hex.mono_cokernelDesc
  have : Epi T.g := by dsimp only [T, cokernelSyzygyShortComplex]; infer_instance
  exact ShortComplex.ShortExact.mk hT

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CokernelSyzygySequence
