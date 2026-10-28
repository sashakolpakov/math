import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CoefficientSubgroupTangentBound
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Subgroup
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Multiplicative
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieEquiv
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafRetracts

/-! # Split Block Lie Bound -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitBlockLieBound.Construction

noncomputable section

/-! The actual multiplicative target subgroup and coefficient preimage
give the Lie-rank inequality for constructed ordinary block splittings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hσ : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)
  (τ : Gal(E/ℚ)) (n : ℕ)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ (q ^ n) = 1)
  {dA rA dB rB : ℕ}
  (eA : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp
    q (n + 1) dA rA)
  (eB : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp
    q 1 dB rB)

include hσ hf eA eB in
theorem splitBlockIsogeny_lieRank_le :
    dB ≤ dA ∧ AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B σ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) dB := by
  let J := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 dB
  let i := OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k eB
  have : IsFinite J.X.hom := (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock_finiteLocallyFree k q 1 dB).1
  have : Subsingleton J.X.left := Subgroup.Construction.subsingleton_of_trivial_relativeFrobenius q k
    (Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k dB)
  have : IsClosedImmersion i.hom.hom.left := OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion_closed k eB
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsCommMonObj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp.X :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).comm
  have : IsCommMonObj J.X := CartierDuality.SheafRetracts.Construction.Retracts.commutative_of_mono i
  let iD : J ⟶ J := 𝟙 J
  have : IsClosedImmersion iD.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (𝟙 J.X.left))
  have hrJ : HodgeConjecture.HeckeCycles.TangentRank.CM.HasRank J dB := HodgeConjecture.HeckeCycles.TangentRank.CM.multiplicative_rank q 0 dB
  obtain ⟨t, ht, hrt⟩ := CoefficientSubgroupTangentBound.Construction.coefficientSubgroup_tangentRank_le j iota hsplit A B ρ σ f hσ
    τ n hf eA J i (OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 1 dB) iD
  have htd : t = dB := HodgeConjecture.HeckeCycles.TangentRank.CM.rank_unique hrt hrJ
  refine ⟨htd ▸ ht, ?_⟩
  exact HodgeConjecture.HeckeCycles.BlockLieEquiv.CM.hasLieRank j iota hsplit B σ τ 0
    (HodgeConjecture.HeckeCycles.EtaleTangents.CM.SplitTangentRank.ordinary_rank q 0 dB rB eB)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitBlockLieBound.Construction
