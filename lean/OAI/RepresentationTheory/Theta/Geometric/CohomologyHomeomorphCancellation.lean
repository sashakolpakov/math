import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

/-! # Cohomology Homeomorph Cancellation -/

namespace OAI.RepresentationTheory.Theta.Geometric.CohomologyHomeomorphCancellation

noncomputable section

/-! Pullback through a genuine homeomorphism is injective on the
original singular cohomology, and cancels in comparisons of two markings. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

variable {X Y Z : TopCat.{0}} {R : Type} [Ring R] (M : ModuleCat.{0} R)

theorem cohomologyPullback_homeomorph_injective (e : X ≃ₜ Y) (n : ℕ) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M (TopCat.ofHom ⟨e, e.continuous⟩) n) :=
  (AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyIsoOfHomotopyEquiv M e.toHomotopyEquiv n).toLinearEquiv.injective

theorem cohomologyPullback_homeomorph_cancel (e : X ≃ₜ Y) (q : X ⟶ Z)
    (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M Y n) (d : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M Z n)
    (h : AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M (TopCat.ofHom ⟨e, e.continuous⟩) n c =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M q n d) :
    c = AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M
      (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩ ≫ q) n d := by
  apply cohomologyPullback_homeomorph_injective M e n
  have he : TopCat.ofHom ⟨e, e.continuous⟩ ≫
      (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩ ≫ q) = q := by
    apply TopCat.ext
    intro x
    exact congrArg q (e.symm_apply_apply x)
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp M (TopCat.ofHom ⟨e, e.continuous⟩)
      (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩ ≫ q) n) d
  rw [he] at hc
  exact h.trans hc

end

end OAI.RepresentationTheory.Theta.Geometric.CohomologyHomeomorphCancellation
