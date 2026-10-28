import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RankSpecialization

/-! # Block Rank Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRankBaseChange

noncomputable section

/-! Scheme ranks of character blocks commute with the actual
base-change comparison, including geometric fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (n : ℕ) (τ : Gal(E/ℚ))

theorem split_block_finite_after_baseChange {S' : Scheme} (p : S' ⟶ S)
    [IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom] :
    IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X.hom := by
  let e := BlocksProjectors.splitBlockBaseChangeIso p n j iota hsplit A ρ τ
  have : IsIso e.inv.left := inferInstanceAs
    (IsIso (((Over.forget S').mapIso e).inv))
  let : IsFinite (BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ)).hom :=
    inferInstanceAs (IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom)
  let : IsFinite ((Over.pullback p).obj
      (BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ))).hom :=
    inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd
      (BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ)).hom p))
  change IsFinite (BlocksProjectors.idempotentBlockScheme (A.pullback p) (ρ.pullback p)
    (q ^ n) (j.projector iota hsplit n τ)).hom
  rw [← e.inv.w]
  infer_instance

theorem split_block_presentation_fiber_rank {k : Type} [Field k]
    (p : Spec (.of k) ⟶ S)
    [IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    [Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    (e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X)
    (x : Spec (.of k)) :
    Module.finrank k H.algebra = (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom.finrank (p x) :=
  RankSpecialization.finite_group_fiber_rank (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom p H
    (e ≪≫ (BlocksProjectors.splitBlockBaseChangeIso p n j iota hsplit A ρ τ).symm) x

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRankBaseChange
