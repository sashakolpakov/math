import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockDivisibility
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteGroupRankIso

/-! # Block Height Rank -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockHeightRank.CM

noncomputable section

/-! Recover the scheme-theoretic rank of the original coefficient block
from the full CMPoints height assertion, using all affine test algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (τ : Gal(E/ℚ))

theorem block_finrank (h : ℕ)
    (hheight : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A ρ (j.localCharacter iota τ) h)
    (n : ℕ) [IsFinite (A.torsionScheme (q ^ n)).hom] (z : Spec (.of k)) :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom.finrank z = q ^ (n * h) := by
  let : IsFinite (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom :=
    PELModuli.CMPoints.FiniteGroupPresentation.idempotentBlock_finite A ρ (q ^ n) (j.projector iota hsplit n τ)
  obtain ⟨G, e, _⟩ := hheight
  obtain ⟨H, u, hu⟩ := PELModuli.CMPoints.FiniteGroupPresentation.split_block_affine_presentation j iota hsplit A ρ n τ
  let : IsMonHom u.hom := hu
  let ep := e n ≪≫ (PELModuli.CMPoints.BlockDivisibility.finiteBlockPointIso j iota hsplit A ρ τ n H u).symm
  let ec : (G.level n).points ≅ H.points :=
    (CommGrpCat.fullyFaithfulForget₂ToGrp.whiskeringRight (CommAlgCat k)).preimageIso ep
  let v := GroupSchemes.FiniteEtale.FiniteCommGroupScheme.schemeIsoOfPoints ec ≪≫ u
  have hv : IsIso v.hom.left := (Over.forget _).map_isIso v.hom
  calc
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X.hom.finrank z =
        (G.level n).scheme.hom.finrank z := by
      rw [← v.hom.w]
      exact (congrFun (Scheme.Hom.finrank_comp_left_of_isIso v.hom.left _) z).symm
    _ = Module.finrank k (G.level n).algebra :=
      AbelianScheme.CartierDuality.Rank.Construction.Schemes.spec_finrank_field k (G.level n).algebra z
    _ = q ^ (n * h) := G.rank n

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockHeightRank.CM
