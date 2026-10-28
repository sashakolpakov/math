import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso

/-! # Base Change Source Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BaseChangeSourceInclusion.Block

noncomputable section

/-! Compose actual block base change and an equivariant source
isomorphism while retaining the original ambient inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S T : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g T)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (b : T ⟶ S) (n : ℕ) (τ : Gal(E/ℚ))
  (e : (A.pullback b).scheme ≅ B.scheme) [hegroup : IsMonHom e.hom]
  (he : (ρ.pullback b).map (j.projector iota hsplit n τ) ≫ e.hom =
    e.hom ≫ σ.map (j.projector iota hsplit n τ))

theorem composedBlock_inclusion :
    ((Intrinsic.BlockBaseChange.nativeBlockBaseChangeGroupIso j iota hsplit A ρ b n τ).hom.hom.hom ≫
      (BlockSourceIso.blockSourceIso (q ^ n) ((ρ.pullback b).map (j.projector iota hsplit n τ))
        (σ.map (j.projector iota hsplit n τ)) e he).hom) ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) =
      (Over.pullback b).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ))) ≫ e.hom := by
  let f := (Intrinsic.BlockBaseChange.nativeBlockBaseChangeGroupIso j iota hsplit A ρ b n τ).hom.hom.hom
  let h := (BlockSourceIso.blockSourceIso (q ^ n) ((ρ.pullback b).map (j.projector iota hsplit n τ))
    (σ.map (j.projector iota hsplit n τ)) e he).hom
  let i := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) ((ρ.pullback b).map (j.projector iota hsplit n τ))
  let k := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ))
  have hs : h ≫ k = i ≫ e.hom := BlockSourceIso.blockSourceIso_inclusion (q ^ n)
    ((ρ.pullback b).map (j.projector iota hsplit n τ)) (σ.map (j.projector iota hsplit n τ)) e he
  have hb : f ≫ i = (Over.pullback b).map
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ))) :=
    (congrArg (fun u => u ≫ i) (Intrinsic.BlockBaseChange.nativeBlockBaseChangeGroupIso_hom j iota hsplit A ρ b n τ)).trans
      (Intrinsic.BlockBaseChange.nativeBlockBaseChangeIso_inclusion j iota hsplit A ρ b n τ)
  exact (Category.assoc f h k).trans ((congrArg (fun u => f ≫ u) hs).trans
    ((Category.assoc f i e.hom).symm.trans (congrArg (fun u => u ≫ e.hom) hb)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BaseChangeSourceInclusion.Block
