import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRankBaseChange

/-! # Relative Block Rank -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockRank

noncomputable section

/-! Ranks of the actual coefficient-block morphisms commute with
arbitrary base change, through their representable point-functor iso. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (n : ℕ) (τ : Gal(E/ℚ))

theorem split_block_locally_free_after_baseChange {S' : Scheme} (p : S' ⟶ S)
    [IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    [Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    [LocallyOfFinitePresentation (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom] :
    IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X.hom ∧
    Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X.hom ∧
    LocallyOfFinitePresentation
      (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X.hom := by
  let e := BlocksProjectors.splitBlockBaseChangeIso p n j iota hsplit A ρ τ
  have : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget S').mapIso e).inv))
  let G := BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ)
  let : IsFinite G.hom := inferInstanceAs (IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom)
  let : Flat G.hom := inferInstanceAs (Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom)
  let : LocallyOfFinitePresentation G.hom := inferInstanceAs
    (LocallyOfFinitePresentation (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom)
  have hf : IsFinite ((Over.pullback p).obj G).hom := inferInstanceAs
    (IsFinite (CategoryTheory.Limits.pullback.snd G.hom p))
  have hflat : Flat ((Over.pullback p).obj G).hom := inferInstanceAs
    (Flat (CategoryTheory.Limits.pullback.snd G.hom p))
  have hfp : LocallyOfFinitePresentation ((Over.pullback p).obj G).hom := inferInstanceAs
    (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd G.hom p))
  change IsFinite (BlocksProjectors.idempotentBlockScheme (A.pullback p) (ρ.pullback p) _ _).hom ∧
    Flat (BlocksProjectors.idempotentBlockScheme (A.pullback p) (ρ.pullback p) _ _).hom ∧
    LocallyOfFinitePresentation (BlocksProjectors.idempotentBlockScheme (A.pullback p) (ρ.pullback p) _ _).hom
  rw [← e.inv.w]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem split_block_baseChange_rank {S' : Scheme} (p : S' ⟶ S)
    [IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    [Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom] (x : S') :
    (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X.hom.finrank x =
      (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom.finrank (p x) := by
  let e := BlocksProjectors.splitBlockBaseChangeIso p n j iota hsplit A ρ τ
  have : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget S').mapIso e).inv))
  let G := BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ)
  let : IsFinite G.hom := inferInstanceAs (IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom)
  let : Flat G.hom := inferInstanceAs (Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom)
  have : IsFinite ((Over.pullback p).obj G).hom := inferInstanceAs
    (IsFinite (CategoryTheory.Limits.pullback.snd G.hom p))
  have : Flat ((Over.pullback p).obj G).hom := inferInstanceAs
    (Flat (CategoryTheory.Limits.pullback.snd G.hom p))
  change (BlocksProjectors.idempotentBlockScheme (A.pullback p) (ρ.pullback p) _ _).hom.finrank x = _
  rw [← e.inv.w]
  exact (congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.inv.left
    ((Over.pullback p).obj G).hom) x).trans (Scheme.Hom.finrank_pullback_snd G.hom p x)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockRank
