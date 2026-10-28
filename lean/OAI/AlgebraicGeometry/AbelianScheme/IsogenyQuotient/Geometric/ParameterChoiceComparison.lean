import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupChoice
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ChoicesFromTorsion

/-! # Parameter Choice Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ParameterChoiceComparison.Construction

noncomputable section

/-! The geometric choice equivalence recovers the actual parameter
pullback of the original subgroup choice, including all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem geometricSupportedChoice_ext
    {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
    (p : A ⟶ A) [IsMonHom p]
    [IsFinite (OppositeKernel.Construction.torsionBlock n p).hom] [Etale (OppositeKernel.Construction.torsionBlock n p).hom]
    (F G : SubgroupFunctor.Construction.SupportedChoice A n M p (Over.mk b))
    (he : ∀ x : Over.mk b ⟶ OppositeKernel.Construction.torsionBlock n p,
      x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈ F.val.subgroup.points (Over.mk b) (𝟙 _) ↔
        x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈ G.val.subgroup.points (Over.mk b) (𝟙 _)) : F = G := by
  apply (BlockChoices.Construction.geometricSupportedChoiceEquiv n M k b p).injective
  apply Subtype.ext
  apply Subgroup.ext
  intro x
  exact (BlockChoices.Construction.geometricSupportedChoiceEquiv_membership n M k b p F x).trans
    ((he x).trans (BlockChoices.Construction.geometricSupportedChoiceEquiv_membership n M k b p G x).symm)

theorem nativeBlockGeometricBaseChangePointsEquiv_inclusion
    {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ) (b : S' ⟶ S)
    (x : Over.mk (𝟙 S') ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    BlockBaseChangeChoices.Construction.nativeBlockGeometricBaseChangePointsEquiv A p n b x ≫ OppositeKernel.Construction.torsionBlockInclusion n p =
      (BlockBaseChangeChoices.Construction.geometricParameterIdentityIso b).inv ≫ A.baseChangePointsMulEquiv b (Over.mk (𝟙 S'))
        (x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)) := by
  change ((BlockBaseChangeChoices.Construction.geometricParameterIdentityIso b).inv ≫ Intrinsic.BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b (Over.mk (𝟙 S')) x) ≫
    OppositeKernel.Construction.torsionBlockInclusion n p = _
  rw [Category.assoc, Intrinsic.BlockBaseChangePoints.Construction.nativeBlockOriginalPoint_inclusion]

set_option backward.isDefEq.respectTransparency false in
theorem parameterChoice_geometric_block_membership
    {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ)
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (b : S' ⟶ S) (F : SubgroupFunctor.Construction.SupportedChoice A.scheme n M p (Over.mk b))
    (x : Over.mk (𝟙 S') ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    BlockBaseChangeChoices.Construction.nativeBlockGeometricBaseChangePointsEquiv A p n b x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈
        F.val.subgroup.points (Over.mk b) (𝟙 _) ↔
      x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p) ∈
        (Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter A (Over.mk b) n M p F).val.subgroup.points (Over.mk (𝟙 S')) (𝟙 _) := by
  rw [nativeBlockGeometricBaseChangePointsEquiv_inclusion, Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter_membership]
  have hb : (BlockBaseChangeChoices.Construction.geometricParameterIdentityIso b).inv ≫ Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk b) (Over.mk (𝟙 S')) = 𝟙 _ :=
    Over.OverMorphism.ext (Category.id_comp (𝟙 S'))
  exact hb ▸ Parameter.TestComparison.Construction.relativeSubgroup_membership_iso F.val.subgroup (BlockBaseChangeChoices.Construction.geometricParameterIdentityIso b).symm
    (Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk b) (Over.mk (𝟙 S')))
    (A.baseChangePointsMulEquiv b (Over.mk (𝟙 S'))
      (x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)))

variable {K : Type} [Field K] [CharZero K] {S : Scheme.{0}} (base : S ⟶ Spec (.of K))
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (p : A.scheme ⟶ A.scheme) [IsMonHom p]
  (n : ℕ) (hn : 0 < n) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
theorem geometricSupportedBaseChange_parameterChoice
    (F : SubgroupFunctor.Construction.SupportedChoice A.scheme n M p (Over.mk b)) :
    ChoicesFromTorsion.Construction.geometricSupportedBaseChangeFromTorsionQuotient base A p n hn k b M
      (Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter A (Over.mk b) n M p F) = F := by
  have hg := ChoicesFromTorsion.Construction.geometricBlockGeometry_from_TorsionQuotient base A p n hn k b
  have : IsFinite (OppositeKernel.Construction.torsionBlock n p).hom := hg.1.1
  have : Etale (OppositeKernel.Construction.torsionBlock n p).hom := hg.1.2
  apply geometricSupportedChoice_ext n M k b p
  intro y
  let x := (BlockBaseChangeChoices.Construction.nativeBlockGeometricBaseChangePointsEquiv A p n b).symm y
  have he := ChoicesFromTorsion.Construction.geometricSupportedBaseChangeFromTorsionQuotient_membership base A p n hn k b M
    (Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter A (Over.mk b) n M p F) x
  have hp := parameterChoice_geometric_block_membership A p n M b F x
  have hh := he.trans hp.symm
  simpa only [x, MulEquiv.apply_symm_apply] using hh

theorem geometricSupportedBaseChange_inverse
    (F : SubgroupFunctor.Construction.SupportedChoice A.scheme n M p (Over.mk b)) :
    (ChoicesFromTorsion.Construction.geometricSupportedBaseChangeFromTorsionQuotient base A p n hn k b M).symm F =
      Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter A (Over.mk b) n M p F := by
  apply (ChoicesFromTorsion.Construction.geometricSupportedBaseChangeFromTorsionQuotient base A p n hn k b M).injective
  exact ((ChoicesFromTorsion.Construction.geometricSupportedBaseChangeFromTorsionQuotient base A p n hn k b M).apply_symm_apply F).trans
    (geometricSupportedBaseChange_parameterChoice base A p n hn M k b F).symm

theorem geometricSupportedBaseChange_inverse_membership
    (F : SubgroupFunctor.Construction.SupportedChoice A.scheme n M p (Over.mk b))
    (U : Over (Spec (.of k))) (t : U ⟶ Over.mk (𝟙 (Spec (.of k)))) (x : U ⟶ (A.pullback b).scheme) :
    x ∈ ((ChoicesFromTorsion.Construction.geometricSupportedBaseChangeFromTorsionQuotient base A p n hn k b M).symm F).val.subgroup.points U t ↔
      A.baseChangePointsMulEquiv b U x ∈ F.val.subgroup.points ((Over.map b).obj U)
        (Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk b) U) := by
  rw [geometricSupportedBaseChange_inverse]
  exact Parameter.SubgroupChoice.Construction.supportedChoiceOverParameter_membership A (Over.mk b) n M p F U t x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ParameterChoiceComparison.Construction
