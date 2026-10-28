import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoefficientExtension

/-! # Coefficient Common Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoefficientCommonExtension

noncomputable section

/-! A finite family of finite coefficient algebras has one finite
coefficient algebra containing all of them. -/

universe u v w
variable {B : Type u} [CommRing B] {A : Type v} [CommRing A] [Algebra B A]

theorem finite_coefficient_common_extension
    (C : Subalgebra B A) [Algebra.FiniteType B C]
    {κ : Type w} [Fintype κ] (D : κ → Subalgebra B A)
    (hD : ∀ i, Algebra.FiniteType B (D i)) :
    ∃ E : Subalgebra B A, C ≤ E ∧ Algebra.FiniteType B E ∧ ∀ i, D i ≤ E := by
  classical
  let E := C ⊔ Finset.univ.sup D
  have hfg : (Finset.univ.sup D).FG := by
    apply Finset.sup_induction Subalgebra.fg_bot
      (fun _ ha _ hb => ha.sup hb)
    intro i _
    exact (Subalgebra.fg_iff_finiteType _).mpr (hD i)
  refine ⟨E, le_sup_left, (Subalgebra.fg_iff_finiteType _).mp
    (((Subalgebra.fg_iff_finiteType C).mpr inferInstance).sup hfg), fun i => ?_⟩
  exact (Finset.le_sup (f := D) (Finset.mem_univ i)).trans le_sup_right

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoefficientCommonExtension
