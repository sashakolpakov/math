import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.BlockBaseChangeChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly

/-! # Choices From Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ChoicesFromTorsion.Construction

noncomputable section

/-! TorsionQuotient supplies every finite-etale premise for geometric choice
base change over an arbitrary characteristic-zero source base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockGeometricBaseChangePointsEquiv_inclusion_left
    {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ) (b : S' ⟶ S)
    (x : Over.mk (𝟙 S') ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    (BlockBaseChangeChoices.Construction.nativeBlockGeometricBaseChangePointsEquiv A p n b x ≫ OppositeKernel.Construction.torsionBlockInclusion n p).left =
      x.left ≫ (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)).left ≫ pullback.fst A.scheme.hom b := by
  change ((𝟙 S') ≫ (Intrinsic.BlockBaseChangePoints.Construction.nativeBlockOriginalPoint A p n b (Over.mk (𝟙 S')) x).left) ≫
    (OppositeKernel.Construction.torsionBlockInclusion n p).left = _
  rw [Category.id_comp]
  exact (congrArg Over.Hom.left (Intrinsic.BlockBaseChangePoints.Construction.nativeBlockOriginalPoint_inclusion A p n b (Over.mk (𝟙 S')) x)).trans
    (Category.assoc _ _ _)

variable {K : Type} [Field K] [CharZero K] {S : Scheme.{0}} (base : S ⟶ Spec (.of K))
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (p : A.scheme ⟶ A.scheme) [IsMonHom p]
  (n : ℕ) (hn : 0 < n) (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)

include base hn in
omit [IsAlgClosed k] in
theorem geometricBlockGeometry_from_TorsionQuotient :
    (IsFinite (OppositeKernel.Construction.torsionBlock n p).hom ∧ Etale (OppositeKernel.Construction.torsionBlock n p).hom) ∧
      (IsFinite (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom ∧
        Etale (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom) :=
  ⟨OppositeKernel.Construction.torsionBlock_finite_etale n p
      (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) base n hn Torsion.Construction.verified_TorsionQuotientInput),
    OppositeKernel.Construction.torsionBlock_finite_etale n ((Over.pullback b).map p)
      (Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := (A.pullback b).scheme) (b ≫ base) n hn Torsion.Construction.verified_TorsionQuotientInput)⟩

variable (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]

def geometricSupportedBaseChangeFromTorsionQuotient :
    SubgroupFunctor.Construction.SupportedChoice (A.pullback b).scheme n M ((Over.pullback b).map p) (Over.mk (𝟙 (Spec (.of k)))) ≃
      SubgroupFunctor.Construction.SupportedChoice A.scheme n M p (Over.mk b) := by
  have hg := geometricBlockGeometry_from_TorsionQuotient base A p n hn k b
  have : IsFinite (OppositeKernel.Construction.torsionBlock n p).hom := hg.1.1
  have : Etale (OppositeKernel.Construction.torsionBlock n p).hom := hg.1.2
  have : IsFinite (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom := hg.2.1
  have : Etale (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom := hg.2.2
  exact BlockBaseChangeChoices.Construction.geometricSupportedBaseChangeEquiv A p n M k b

theorem geometricSupportedBaseChangeFromTorsionQuotient_membership
    (F : SubgroupFunctor.Construction.SupportedChoice (A.pullback b).scheme n M ((Over.pullback b).map p) (Over.mk (𝟙 (Spec (.of k)))))
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    BlockBaseChangeChoices.Construction.nativeBlockGeometricBaseChangePointsEquiv A p n b x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈
        (geometricSupportedBaseChangeFromTorsionQuotient base A p n hn k b M F).val.subgroup.points (Over.mk b) (𝟙 _) ↔
      x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p) ∈ F.val.subgroup.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _) := by
  have hg := geometricBlockGeometry_from_TorsionQuotient base A p n hn k b
  have : IsFinite (OppositeKernel.Construction.torsionBlock n p).hom := hg.1.1
  have : Etale (OppositeKernel.Construction.torsionBlock n p).hom := hg.1.2
  have : IsFinite (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom := hg.2.1
  have : Etale (OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)).hom := hg.2.2
  exact BlockBaseChangeChoices.Construction.geometricSupportedBaseChangeEquiv_membership A p n M k b F x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.ChoicesFromTorsion.Construction
