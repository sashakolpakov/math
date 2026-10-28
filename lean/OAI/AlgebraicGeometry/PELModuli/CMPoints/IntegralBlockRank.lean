import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockRank
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentHeight
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct

/-! # Integral Block Rank -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

section

/-! The connected component rank computation determines the rank of
the universal block at every point of the entire integral PEL model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

theorem IntegralBlockRank.split_block_finite_locally_free_of_torsion (ht : PolarizedTorsionFiniteness.TorsionFiniteLocallyFree A q)
    (n : ℕ) (τ : Gal(E/ℚ)) :
    IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom ∧
    Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom ∧
    LocallyOfFinitePresentation (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := by
  obtain ⟨hf, hflat, hfp⟩ := ht n
  let : IsFinite (A.torsionScheme (q ^ n)).hom := hf
  let : Flat (A.torsionScheme (q ^ n)).hom := hflat
  let : LocallyOfFinitePresentation (A.torsionScheme (q ^ n)).hom := hfp
  exact RelativeBlockFlatness.split_block_finite_locally_free j iota hsplit A ρ n τ

theorem IntegralBlockRank.connected_block_morphism_rank_from_complex [ConnectedSpace S]
    (ht : PolarizedTorsionFiniteness.TorsionFiniteLocallyFree A q) (pC : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) (n : ℕ) (τ : Gal(E/ℚ))
    (r : ℕ) (hcard : Nat.card (BlocksProjectors.blockPoints (A.pullback pC) (ρ.pullback pC)
      (j.localCharacter iota τ) n (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = r)
    (y : S) : (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom.finrank y = r := by
  obtain ⟨hf, hflat, hfp⟩ := IntegralBlockRank.split_block_finite_locally_free_of_torsion j iota hsplit A ρ ht n τ
  let : IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hf
  let : Flat (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hflat
  let : LocallyOfFinitePresentation (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hfp
  let GC := BlocksProjectors.splitBlockGroupScheme j iota hsplit (A.pullback pC) (ρ.pullback pC) n τ
  let : IsFinite GC.X.hom := BlockRankBaseChange.split_block_finite_after_baseChange j iota hsplit A ρ n τ pC
  obtain ⟨HC, eC, _⟩ := FiniteGroupPresentation.finite_group_affine_presentation GC
  let xc : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let F := (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom
  calc
    F.finrank y = F.finrank (pC xc) := F.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = Module.finrank ℂ HC.algebra :=
      (BlockRankBaseChange.split_block_presentation_fiber_rank j iota hsplit A ρ n τ pC HC eC xc).symm
    _ = r := (ComplexBlockRank.complex_block_presentation_rank_eq_card j iota hsplit
      (A.pullback pC) (ρ.pullback pC) n τ HC eC).trans hcard

variable [NumberField.IsCMField E] (M : Models.RankThreePELModel E K)

theorem Models.RankThreePELModel.exists_integral_block_rank_bound (hM : M.HasPrescribedBallPeriods) :
    ∃ D : ℕ, ∀ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      ∀ (j : M.QadicChoice q) (hsplit : j.HasSplitCoordinates M.extendedEmbedding), D < q →
        ∀ (a : M.Family) (n : ℕ) (τ : Gal(E/ℚ)) (y : (M.integral a).toOver.left),
          (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit
            (M.integral a).universal.data.polarized.abelian
            (M.integral a).universal.data.action n τ).X.hom.finrank y = q ^ (n * 3) := by
  obtain ⟨D, hD⟩ := M.exists_component_complex_block_bound hM
  refine ⟨D, fun q hq => ?_⟩
  let : Fact q.Prime := ⟨hq⟩
  intro j hsplit hb a n τ y
  obtain ⟨t, z, hz⟩ := IntegralModel.Coproduct.decomposition_cover (M.components a).S (M.decomposition a) y
  let A := (M.integral a).universal.data.polarized.abelian
  let ρ := (M.integral a).universal.data.action
  obtain ⟨hf, hflat, _⟩ := IntegralBlockRank.split_block_finite_locally_free_of_torsion
    j M.extendedEmbedding hsplit A ρ
    (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free (M.integral a).universal.data.polarized hq.pos) n τ
  let : IsFinite (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit A ρ n τ).X.hom := hf
  let : Flat (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit A ρ n τ).X.hom := hflat
  let : ConnectedSpace ((M.components a).S t).left := M.integralComponent_connected hM a t
  have hc := IntegralBlockRank.connected_block_morphism_rank_from_complex j M.extendedEmbedding hsplit
    (M.componentAbelian a t) (M.componentAction a t)
    (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free (M.componentPolarized a t) hq.pos) (M.componentComplexSection a t)
    n τ (q ^ (3 * n)) (hD q hq j hsplit hb a t n τ) z
  have hr := RelativeBlockRank.split_block_baseChange_rank j M.extendedEmbedding hsplit A ρ n τ
    (M.integralComponentInclusion a t).left z
  change _ = (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit A ρ n τ).X.hom.finrank
    ((M.integralComponentInclusion a t).left z) at hr
  rw [show (M.integralComponentInclusion a t).left z = y from hz] at hr
  exact hr.symm.trans (hc.trans (congrArg (fun m : ℕ => q ^ m) (Nat.mul_comm 3 n)))

end

/-! A common bound gives height three on the exact geometric fibers
used in CMPoints. Ranks pass through the actual geometric-base pullback and
the algebraic closure of each point's residue field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

theorem Models.RankThreePELModel.exists_reduction_height_bound (hM : M.HasPrescribedBallPeriods)
    :
    ∃ D : ℕ, ∀ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      ∀ (j : M.QadicChoice q) (_hsplit : j.HasSplitCoordinates M.extendedEmbedding), D < q →
        ∀ (R : M.GoodIntegralReduction q j) (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)),
          BlocksProjectors.BlockHasHeight (R.fiberAbelian a x) (R.fiberAction a x)
            (j.localCharacter M.extendedEmbedding τ) 3 := by
  obtain ⟨D, hD⟩ := M.exists_integral_block_rank_bound hM
  refine ⟨D, fun q hq => ?_⟩
  let : Fact q.Prime := ⟨hq⟩
  intro j hsplit hb R a x τ
  have hex (n : ℕ) : ∃ H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme (R.fiberField a x),
      ∃ e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit
        (R.fiberAbelian a x) (R.fiberAction a x) n τ).X,
        IsMonHom e.hom ∧ Module.finrank (R.fiberField a x) H.algebra = q ^ (n * 3) := by
    let A := (M.integral a).universal.data.polarized.abelian
    let ρ := (M.integral a).universal.data.action
    obtain ⟨hfI, hflatI, _⟩ := IntegralBlockRank.split_block_finite_locally_free_of_torsion
      j M.extendedEmbedding hsplit A ρ
      (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free (M.integral a).universal.data.polarized hq.pos) n τ
    let : IsFinite (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit A ρ n τ).X.hom := hfI
    let : Flat (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit A ρ n τ).X.hom := hflatI
    obtain ⟨hfR, hflatR, _⟩ := IntegralBlockRank.split_block_finite_locally_free_of_torsion
      j M.extendedEmbedding hsplit (R.abelian a) (R.action a)
      (PolarizedTorsionFiniteness.polarized_torsion_finite_locally_free (R.polarized a) hq.pos) n τ
    let : IsFinite (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit (R.abelian a) (R.action a) n τ).X.hom := hfR
    let : Flat (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit (R.abelian a) (R.action a) n τ).X.hom := hflatR
    let G := BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit (R.fiberAbelian a x) (R.fiberAction a x) n τ
    let : IsFinite G.X.hom := BlockRankBaseChange.split_block_finite_after_baseChange j M.extendedEmbedding hsplit
      (R.abelian a) (R.action a) n τ (R.fiberMap a x)
    obtain ⟨H, e, he⟩ := FiniteGroupPresentation.finite_group_affine_presentation G
    refine ⟨H, e, he, ?_⟩
    let xk : Spec (.of (R.fiberField a x)) := IsLocalRing.closedPoint (R.fiberField a x)
    calc
      Module.finrank (R.fiberField a x) H.algebra =
          (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit (R.abelian a) (R.action a) n τ).X.hom.finrank
            (R.fiberMap a x xk) :=
        BlockRankBaseChange.split_block_presentation_fiber_rank j M.extendedEmbedding hsplit (R.abelian a) (R.action a)
          n τ (R.fiberMap a x) H e xk
      _ = (BlocksProjectors.splitBlockGroupScheme j M.extendedEmbedding hsplit A ρ n τ).X.hom.finrank
          (R.projection a (R.fiberMap a x xk)) :=
        RelativeBlockRank.split_block_baseChange_rank j M.extendedEmbedding hsplit A ρ n τ (R.projection a) (R.fiberMap a x xk)
      _ = q ^ (n * 3) := hD q hq j hsplit hb a n τ _
  choose H e he hrank using hex
  let : ∀ n, IsMonHom (e n).hom := he
  exact BlockDivisibility.blockHasHeight_of_finite_presentations j M.extendedEmbedding hsplit
    (R.fiberAbelian a x) (R.fiberAction a x) τ H e 3 hrank

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
