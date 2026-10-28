import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps

/-! # CM Points Block Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison

noncomputable section

/-! The IsogenyQuotient fixed-kernel block and CMPoints's character-defined block
have the same original inclusion and compatible group structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (n : ℕ) (τ : Gal(E/ℚ))

abbrev l45BlockInclusion :=
  PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A σ (q ^ n) (j.projector iota hsplit n τ)

theorem l45BlockInclusion_isMonHom :
    letI : GrpObj (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A σ (q ^ n) (j.projector iota hsplit n τ)) :=
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ n τ).grp
    IsMonHom (l45BlockInclusion j iota hsplit A σ n τ) := by
  let : GrpObj (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A σ (q ^ n) (j.projector iota hsplit n τ)) :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ n τ).grp
  let e := yonedaGrpObjIsoOfRepresentableBy
    (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A σ (q ^ n) (j.projector iota hsplit n τ))
    (PELModuli.CMPoints.BlocksProjectors.blockFunctor A σ (j.localCharacter iota τ) n)
    (PELModuli.CMPoints.BlocksProjectors.splitBlockRepresentable j iota hsplit A σ n τ)
  apply AbelianScheme.IsogenyQuotient.GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    exact congrArg Subtype.val ((e.hom.app (.op T)).hom.map_one)
  · intro T a b
    exact congrArg Subtype.val ((e.hom.app (.op T)).hom.map_mul a b)

theorem l45NativeBlockIso_inclusion :
    (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A σ n τ).hom ≫
      l45BlockInclusion j iota hsplit A σ n τ =
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) := by
  have h : (PELModuli.CMPoints.BlocksProjectors.splitBlockRepresentable j iota hsplit A σ n τ).homEquiv
      (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A σ n τ).hom =
        (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockRepresentable j iota hsplit A σ n τ).homEquiv (𝟙 _) :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockRepresentable j iota hsplit A σ n τ).homEquiv.apply_symm_apply _
  have h' := congrArg Subtype.val h
  change (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A σ n τ).hom ≫
    l45BlockInclusion j iota hsplit A σ n τ =
      (𝟙 _) ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) at h'
  exact h'.trans (Category.id_comp _)

theorem l45NativeBlockIso_group :
    letI : GrpObj (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A σ (q ^ n) (j.projector iota hsplit n τ)) :=
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ n τ).grp
    IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A σ n τ).hom := by
  let : GrpObj (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A σ (q ^ n) (j.projector iota hsplit n τ)) :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ n τ).grp
  have : Mono (l45BlockInclusion j iota hsplit A σ n τ) := by
    apply Over.mono_of_mono_left
  have : IsMonHom (l45BlockInclusion j iota hsplit A σ n τ) :=
    l45BlockInclusion_isMonHom j iota hsplit A σ n τ
  apply AbelianScheme.IsogenyQuotient.GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    apply (cancel_mono (l45BlockInclusion j iota hsplit A σ n τ)).mp
    simp only [Category.assoc, l45NativeBlockIso_inclusion, MonObj.one_comp]
  · intro T a b
    apply (cancel_mono (l45BlockInclusion j iota hsplit A σ n τ)).mp
    simp only [Category.assoc, l45NativeBlockIso_inclusion, MonObj.mul_comp]

def nativeCMPointsBlockGroupIso :
    Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ))) ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ n τ).toGrp := by
  letI : GrpObj (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A σ (q ^ n) (j.projector iota hsplit n τ)) :=
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A σ n τ).grp
  have : IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A σ n τ).hom :=
    l45NativeBlockIso_group j iota hsplit A σ n τ
  exact Grp.mkIso' (AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A σ n τ)

theorem nativeCMPointsBlockGroupIso_inclusion :
    (nativeCMPointsBlockGroupIso j iota hsplit A σ n τ).hom.hom.hom ≫
      l45BlockInclusion j iota hsplit A σ n τ =
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (σ.map (j.projector iota hsplit n τ)) :=
  l45NativeBlockIso_inclusion j iota hsplit A σ n τ

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison
