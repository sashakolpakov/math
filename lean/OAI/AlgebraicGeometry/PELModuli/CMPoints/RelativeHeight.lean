import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRankBaseChange
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockRank
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockFlatness
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDivisibility

/-! # Relative Height -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeHeight

noncomputable section

/-! A complex block count fixes the height on a connected family once
the ambient abelian torsion is finite locally free. This assembles the
actual FiniteEtale tower on each fiber; no block-flatness or divisibility datum
is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} [ConnectedSpace S] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (pC : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (τ : Gal(E/ℚ))

theorem connected_block_rank_from_complex {k : Type} [Field k]
    (p : Spec (.of k) ⟶ S) (n r : ℕ)
    [IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    [Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    [LocallyOfFinitePresentation (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom]
    (hcard : Nat.card (BlocksProjectors.blockPoints (A.pullback pC) (ρ.pullback pC) (j.localCharacter iota τ) n
      (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = r)
    (H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    (e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X) :
    Module.finrank k H.algebra = r := by
  let GC := BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback pC) (ρ.pullback pC) n τ
  let : IsFinite GC.X.hom := BlockRankBaseChange.split_block_finite_after_baseChange j iota hsplit A ρ n τ pC
  obtain ⟨HC, eC, _⟩ := FiniteGroupPresentation.finite_group_affine_presentation GC
  let xc : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let xk : Spec (.of k) := IsLocalRing.closedPoint k
  let F := (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom
  calc
    Module.finrank k H.algebra = F.finrank (p xk) :=
      BlockRankBaseChange.split_block_presentation_fiber_rank j iota hsplit A ρ n τ p H e xk
    _ = F.finrank (pC xc) := F.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = Module.finrank ℂ HC.algebra :=
      (BlockRankBaseChange.split_block_presentation_fiber_rank j iota hsplit A ρ n τ pC HC eC xc).symm
    _ = r := (ComplexBlockRank.complex_block_presentation_rank_eq_card j iota hsplit
      (A.pullback pC) (ρ.pullback pC) n τ HC eC).trans hcard

include hsplit in
theorem blockHasHeight_of_connected_finite_flat_torsion
    [∀ n : ℕ, IsFinite (A.torsionScheme (q ^ n)).hom]
    [∀ n : ℕ, Flat (A.torsionScheme (q ^ n)).hom]
    [∀ n : ℕ, LocallyOfFinitePresentation (A.torsionScheme (q ^ n)).hom]
    (h : ℕ) (hcard : ∀ n : ℕ,
      Nat.card (BlocksProjectors.blockPoints (A.pullback pC) (ρ.pullback pC) (j.localCharacter iota τ) n
        (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = q ^ (n * h))
    {k : Type} [Field k] (p : Spec (.of k) ⟶ S) :
    BlocksProjectors.BlockHasHeight (A.pullback p) (ρ.pullback p) (j.localCharacter iota τ) h := by
  have hex (n : ℕ) : ∃ H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k,
      ∃ e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ).X,
        IsMonHom e.hom ∧ Module.finrank k H.algebra = q ^ (n * h) := by
    obtain ⟨hf, hflat, hfp⟩ := RelativeBlockFlatness.split_block_finite_locally_free j iota hsplit A ρ n τ
    let : IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hf
    let : Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hflat
    let : LocallyOfFinitePresentation (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hfp
    let G := BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback p) (ρ.pullback p) n τ
    let : IsFinite G.X.hom := BlockRankBaseChange.split_block_finite_after_baseChange j iota hsplit A ρ n τ p
    obtain ⟨H, e, he⟩ := FiniteGroupPresentation.finite_group_affine_presentation G
    exact ⟨H, e, he, connected_block_rank_from_complex j iota hsplit A ρ pC τ p n
      (q ^ (n * h)) (hcard n) H e⟩
  choose H e he hrank using hex
  let : ∀ n, IsMonHom (e n).hom := he
  exact BlockDivisibility.blockHasHeight_of_finite_presentations j iota hsplit (A.pullback p) (ρ.pullback p) τ H e h hrank

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeHeight
