import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentHeightBound
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralComponents
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Multiplication

/-! # Component Height -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! One bound makes the actual blocks on every supplied integral
component have height three. The general abelian multiplication theorem
is an explicit additional background input; the complex ranks and the
FiniteEtale towers are constructed here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

theorem Models.RankThreePELModel.exists_component_height_bound (hM : M.HasPrescribedBallPeriods)
    :
    ∃ D : ℕ, ∀ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      ∀ j : M.QadicChoice q, j.HasSplitCoordinates M.extendedEmbedding → D < q →
        ∀ (a : M.Family) (t : Fin (M.componentCount a)) (k : Type) [Field k]
          (p : Spec (.of k) ⟶ ((M.components a).S t).left) (τ : Gal(E/ℚ)),
          BlocksProjectors.BlockHasHeight ((M.componentAbelian a t).pullback p) ((M.componentAction a t).pullback p)
            (j.localCharacter M.extendedEmbedding τ) 3 := by
  obtain ⟨D, hD⟩ := M.exists_component_complex_block_bound hM
  refine ⟨D, fun q hq => ?_⟩
  let : Fact q.Prime := ⟨hq⟩
  intro j hsplit hb a t k hk p τ
  let : ConnectedSpace ((M.components a).S t).left := M.integralComponent_connected hM a t
  exact Multiplication.blockHasHeight_of_torsion_finite_locally_free j M.extendedEmbedding hsplit
    (M.componentAbelian a t)
    (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free (M.componentPolarized a t) hq.pos) (M.componentAction a t) (M.componentComplexSection a t) τ 3
    (fun n => (hD q hq j hsplit hb a t n τ).trans
      (congrArg (fun m : ℕ => q ^ m) (Nat.mul_comm 3 n))) p

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
