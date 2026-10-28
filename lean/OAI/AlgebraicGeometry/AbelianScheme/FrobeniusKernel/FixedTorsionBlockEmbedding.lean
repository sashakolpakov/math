import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Fixed Torsion Block Embedding -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedTorsionBlockEmbedding.Construction

noncomputable section

/-! An actual closed group inclusion killed at one torsion level and
fixed by the original coefficient projector embeds into that native block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (n : ℕ) (τ : Gal(E/ℚ)) (G : Grp (Over S))
  (i : G.X ⟶ A.scheme)
  (hk : i ^ (q ^ n) = 1) (he : i ≫ ρ.map (j.projector iota hsplit n τ) = i)

def fixedTorsionBlockLift : G.X ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X :=
  (PELModuli.CMPoints.BlocksProjectors.idempotentBlockPointsEquiv A ρ (q ^ n) (j.projector iota hsplit n τ) G.X).symm ⟨i, hk, he⟩

theorem fixedTorsionBlockLift_inclusion :
    fixedTorsionBlockLift j iota hsplit A ρ n τ G i hk he ≫ CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ = i :=
  congrArg Subtype.val ((PELModuli.CMPoints.BlocksProjectors.idempotentBlockPointsEquiv A ρ (q ^ n)
    (j.projector iota hsplit n τ) G.X).apply_symm_apply ⟨i, hk, he⟩)

variable [IsMonHom i]

instance fixedTorsionBlockLift_group :
    IsMonHom (fixedTorsionBlockLift j iota hsplit A ρ n τ G i hk he) := by
  have : Mono (CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ) :=
    inferInstanceAs (Mono (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ n) (j.projector iota hsplit n τ)))
  have : IsMonHom (fixedTorsionBlockLift j iota hsplit A ρ n τ G i hk he ≫
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ) := by
    rw [fixedTorsionBlockLift_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ)

def fixedTorsionBlockEmbedding : G ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp :=
  Grp.homMk (fixedTorsionBlockLift j iota hsplit A ρ n τ G i hk he)

theorem fixedTorsionBlockEmbedding_closed [IsClosedImmersion i.left] :
    IsClosedImmersion (fixedTorsionBlockEmbedding j iota hsplit A ρ n τ G i hk he).hom.hom.left := by
  have hi : IsClosedImmersion i.left := inferInstance
  have h := congrArg Over.Hom.left (fixedTorsionBlockLift_inclusion j iota hsplit A ρ n τ G i hk he)
  have : IsClosedImmersion ((fixedTorsionBlockLift j iota hsplit A ρ n τ G i hk he).left ≫
      (CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ).left) := (congrArg IsClosedImmersion h).mpr hi
  have : IsClosedImmersion (CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ).left :=
    inferInstanceAs (IsClosedImmersion
      (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ n) (j.projector iota hsplit n τ)).left)
  exact IsClosedImmersion.of_comp (fixedTorsionBlockLift j iota hsplit A ρ n τ G i hk he).left
    (CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ).left

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FixedTorsionBlockEmbedding.Construction
