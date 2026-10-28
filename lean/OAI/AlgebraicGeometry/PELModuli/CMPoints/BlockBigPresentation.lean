import OAI.AlgebraicGeometry.PELModuli.CMPoints.HeightUniqueness
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralBlockRank

/-! # Block Big Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockBigPresentation

noncomputable section

/-! The affine FiniteEtale definition of block height supplies an equivalent
tower represented on the whole big scheme site. We use the actual
finite block schemes and recover their ranks from the affine comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

include hsplit in
theorem block_big_presentation_of_height (ht : PolarizedTorsionFiniteness.TorsionFiniteLocallyFree A q)
    (τ : Gal(E/ℚ)) (h : ℕ) (hh : BlocksProjectors.BlockHasHeight A ρ (j.localCharacter iota τ) h) :
    ∃ G : GroupSchemes.FiniteEtale.PDivisibleGroup k q h,
      Nonempty (∀ n, yonedaGrp.obj (Grp.mk (G.level n).scheme) ≅
        BlocksProjectors.blockFunctor A ρ (j.localCharacter iota τ) n) := by
  obtain ⟨G₀, e₀, _⟩ := hh
  have hex (n : ℕ) : ∃ H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k,
      ∃ e : H.scheme ≅ (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X,
        IsMonHom e.hom ∧ Module.finrank k H.algebra = q ^ (n * h) := by
    obtain ⟨hf, _, _⟩ := IntegralBlockRank.split_block_finite_locally_free_of_torsion j iota hsplit A ρ ht n τ
    let : IsFinite (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom := hf
    obtain ⟨H, e, he⟩ := FiniteGroupPresentation.finite_group_affine_presentation (BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ)
    let : IsMonHom e.hom := he
    let f := GroupSchemes.FiniteEtale.FiniteCommGroupScheme.schemeIsoOfPoints
      (HeightUniqueness.commutativePointIsoOfGroupIso
        (BlockDivisibility.finiteBlockPointIso j iota hsplit A ρ τ n H e ≪≫ (e₀ n).symm))
    exact ⟨H, e, he, (RankSpecialization.finite_group_rank_of_iso H (G₀.level n) f).trans (G₀.rank n)⟩
  choose H e he hrank using hex
  let : ∀ n, IsMonHom (e n).hom := he
  let G := BlockDivisibility.blockDivisibleGroupOfRanks j iota hsplit A ρ τ H e h hrank
  refine ⟨G, ⟨fun n => ?_⟩⟩
  exact yonedaGrp.mapIso (Grp.mkIso' (e n)) ≪≫ BlockSchemeTower.blockYonedaIso j iota hsplit A ρ n τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockBigPresentation
