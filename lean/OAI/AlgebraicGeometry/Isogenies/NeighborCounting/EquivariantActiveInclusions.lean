import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantBlockIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveSplittingSourceTransport

/-! # Equivariant Active Inclusions -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions

noncomputable section

/-! Active source coordinates transported through an equivariant
abelian isomorphism retain the actual ambient plane and line inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (k : Type) [Field k] {g : ℕ}
  (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (c : AbelianScheme.FrobeniusKernel.PolarizedComponents.Construction.EquivariantAbelianIso A B ρ σ) (τ : Gal(E/ℚ))
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ 1 τ).toGrp)

local notation "b" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EquivariantBlockIso.Construction.equivariantAbelianBlockIso j iota hsplit A B ρ σ c 1 τ

theorem active_plane_ambient_source_transport :
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (b ≪≫ e)).hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ ≫ c.abelian.hom =
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q e).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ := by
  let : IsMonHom c.abelian.hom := c.preservesGroup
  have hb := AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso.Construction.l45NativeBlockSourceIso_inclusion j iota hsplit A B ρ σ c.abelian c.action 1 τ
  have he := congrArg (fun f => f.hom.hom) (AbelianScheme.FrobeniusKernel.ActiveSplittingSourceTransport.Construction.chosenActiveEtalePlane_sourceTransport k q b e)
  calc
    _ = (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (b ≪≫ e)).hom.hom ≫
        (b).hom.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ :=
      congrArg (fun f => (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q (b ≪≫ e)).hom.hom ≫ f) hb.symm
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ) he)

theorem active_line_ambient_source_transport (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q (b ≪≫ e) L).hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ ≫ c.abelian.hom =
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e L).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ := by
  let : IsMonHom c.abelian.hom := c.preservesGroup
  have hb := AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso.Construction.l45NativeBlockSourceIso_inclusion j iota hsplit A B ρ σ c.abelian c.action 1 τ
  have he := congrArg (fun f => f.hom.hom) (AbelianScheme.FrobeniusKernel.ActiveSplittingSourceTransport.Construction.chosenActiveEtaleLine_sourceTransport k q b e L)
  calc
    _ = (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q (b ≪≫ e) L).hom.hom ≫
        (b).hom.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ :=
      congrArg (fun f => (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q (b ≪≫ e) L).hom.hom ≫ f) hb.symm
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ 1 τ) he)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EquivariantActiveInclusions
