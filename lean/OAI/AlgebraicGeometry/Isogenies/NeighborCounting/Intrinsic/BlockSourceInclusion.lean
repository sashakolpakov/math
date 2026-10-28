import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso

/-! # Block Source Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockSourceInclusion

noncomputable section

/-! A base change followed by an actual equivariant source isomorphism
retains the original torsion-block inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S T : Scheme} {g h : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h T)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (f : T ⟶ S) (e : (A.pullback f).scheme ≅ B.scheme) [IsMonHom e.hom]
  (n : ℕ) (τ : Gal(E/ℚ))
  (he : (ρ.pullback f).map (j.projector iota hsplit n τ) ≫ e.hom =
    e.hom ≫ σ.map (j.projector iota hsplit n τ))

include he in
theorem nativeBlockSourceIso_inclusion :
    ((BlockBaseChange.nativeBlockBaseChangeGroupIso j iota hsplit A ρ f n τ) ≪≫
      BlockSourceIso.blockSourceGroupIso (q ^ n) ((ρ.pullback f).map (j.projector iota hsplit n τ))
        (σ.map (j.projector iota hsplit n τ)) e he).hom.hom.hom ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) =
    (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ))) ≫ e.hom := by
  change ((BlockBaseChange.nativeBlockBaseChangeIso j iota hsplit A ρ f n τ).hom ≫
      (BlockSourceIso.blockSourceIso (q ^ n) ((ρ.pullback f).map (j.projector iota hsplit n τ))
        (σ.map (j.projector iota hsplit n τ)) e he).hom) ≫ _ = _
  rw [Category.assoc, BlockSourceIso.blockSourceIso_inclusion, ← Category.assoc,
    BlockBaseChange.nativeBlockBaseChangeIso_inclusion]
  rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockSourceInclusion
