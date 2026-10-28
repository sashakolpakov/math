import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockSubgroupBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingIsoAnnihilator

/-! # Block Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockPairingBaseChange.Construction

noncomputable section

/-! The opposite annihilator commutes with actual parameter pullback,
using the original block pairing and the native block isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (p q : A.scheme ⟶ A.scheme) [IsMonHom p] [IsMonHom q] (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
def nativeBlockPairingPullback {S' : Scheme.{0}} (b : S' ⟶ S)
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n p) (B := OppositeKernel.Construction.torsionBlock n q)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p))
      (B := OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map q)) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S').X) :=
  (PairingBaseChange.Construction.nativePairingPullback b (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) (Grp.mk (OppositeKernel.Construction.torsionBlock n q)) e).restrict
    (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n b).hom (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A q n b).hom

set_option backward.isDefEq.respectTransparency false in
theorem oppositeKernel_parameterBaseChange (P : Over S)
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n p) (B := OppositeKernel.Construction.torsionBlock n q)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P (OppositeKernel.Construction.oppositeKernel n p q e F) =
      OppositeKernel.Construction.oppositeKernel n ((Over.pullback P.hom).map p) ((Over.pullback P.hom).map q)
        (nativeBlockPairingPullback A p q n P.hom e)
        (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P F) := by
  let H := SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n p) F
  let ep := PairingBaseChange.Construction.nativePairingPullback P.hom (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) (Grp.mk (OppositeKernel.Construction.torsionBlock n q)) e
  have hparam := Parameter.AnnihilatorComparison.Construction.relativeParameter_annihilator_comparison (Grp.mk (OppositeKernel.Construction.torsionBlock n p))
    (Grp.mk (OppositeKernel.Construction.torsionBlock n q)) P H e
  have hiso := ep.restrict_annihilator_iso (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A p n P.hom).hom
    (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A q n P.hom).hom
    (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk (OppositeKernel.Construction.torsionBlock n p)) P H)
  have hsub := BlockSubgroupBaseChange.Construction.parameter_nativeBlock_subgroup_comparison A P p n F
  have hann := (congrArg (SubgroupTransport.Construction.relativeSubgroupPullback (BlockBaseChangeGroup.Construction.nativeBlockBaseChangeIso A q n P.hom).hom) hparam).trans
    (hiso.symm.trans (congrArg (nativeBlockPairingPullback A p q n P.hom e).relativeAnnihilator hsub))
  exact (BlockSubgroupBaseChange.Construction.parameter_nativeBlock_image_comparison A P q n (e.relativeAnnihilator H)).trans
    (congrArg (SubgroupTransport.Construction.relativeSubgroupImage (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback P.hom).map q))) hann)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockPairingBaseChange.Construction
