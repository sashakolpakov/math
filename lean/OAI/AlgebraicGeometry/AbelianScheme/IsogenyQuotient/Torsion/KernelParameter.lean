import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingIsoAnnihilator

/-! # Kernel Parameter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.KernelParameter.Construction

noncomputable section

/-!
The exact original torsion subgroup becomes the torsion subgroup of the
native family over its parameter. Self-annihilation is preserved under
this canonical comparison, including on nonreduced parameter schemes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (P : Over S)
  (n : ℕ) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P)

theorem nativeTorsionParameterPoint_inclusion
    (U : Over P.left)
    (x : U ⟶ (SheafComparison.Construction.kernelTorsionGroup ((Over.pullback P.hom).mapGrp.obj G) n).X) :
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom (SheafComparison.Construction.kernelTorsionGroup G n) U).symm
        (x ≫ (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso P.hom G n).inv.hom.hom) ≫
      Groups.Construction.nativeTorsionInclusion G.X n =
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm
      (x ≫ Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n) := by
  have hn := CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom (SheafComparison.Construction.kernelTorsionInclusion G n) U
    (x ≫ (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso P.hom G n).inv.hom.hom)
  have hi : (x ≫ (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso P.hom G n).inv.hom.hom) ≫
      ((Over.pullback P.hom).mapGrp.map (SheafComparison.Construction.kernelTorsionInclusion G n)).hom.hom =
      x ≫ Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => x ≫ k) (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeIso_inv_inclusion P.hom G n))
  exact hn.symm.trans (congrArg (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm hi)

theorem nativeTorsionSubgroupOverParameter_comparison :
    SubgroupTransport.Construction.relativeSubgroupPullback (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso P.hom G n).inv.hom.hom
      (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (SheafComparison.Construction.kernelTorsionGroup G n) P
        (SubgroupTransport.Construction.relativeSubgroupPullback (SheafComparison.Construction.kernelTorsionInclusion G n).hom.hom F)) =
    SubgroupTransport.Construction.relativeSubgroupPullback (Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n)
      (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) := by
  ext U t x
  exact iff_of_eq (congrArg
    (fun z => z ∈ F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U))
    (nativeTorsionParameterPoint_inclusion G P n U x))

theorem nativeTorsionSubgroupOverParameter_self_annihilating
    (e : Annihilator.Construction.SchemeBicharacter (A := Groups.Construction.nativeTorsionScheme G.X n) (B := Groups.Construction.nativeTorsionScheme G.X n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (h : e.relativeAnnihilator (SubgroupTransport.Construction.relativeSubgroupPullback (Groups.Construction.nativeTorsionInclusion G.X n) F) =
      SubgroupTransport.Construction.relativeSubgroupPullback (Groups.Construction.nativeTorsionInclusion G.X n) F) :
    let H := SubgroupTransport.Construction.relativeSubgroupPullback
      (Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n)
      (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F)
    (Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom G G n e).relativeAnnihilator H = H := by
  let H := SubgroupTransport.Construction.relativeSubgroupPullback (SheafComparison.Construction.kernelTorsionInclusion G n).hom.hom F
  let HP := Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (SheafComparison.Construction.kernelTorsionGroup G n) P H
  let ep := PairingBaseChange.Construction.nativePairingPullback P.hom (SheafComparison.Construction.kernelTorsionGroup G n) (SheafComparison.Construction.kernelTorsionGroup G n) e
  have hep : ep.relativeAnnihilator HP = HP :=
    (Parameter.AnnihilatorComparison.Construction.relativeParameter_annihilator_comparison (SheafComparison.Construction.kernelTorsionGroup G n) (SheafComparison.Construction.kernelTorsionGroup G n)
      P H e).symm.trans (congrArg (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (SheafComparison.Construction.kernelTorsionGroup G n) P) h)
  have hi := nativeTorsionSubgroupOverParameter_comparison G P n F
  have hr := ep.restrict_annihilator_iso
    (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso P.hom G n).inv.hom.hom
    (Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso P.hom G n).inv.hom.hom HP
  rw [hep] at hr
  exact (congrArg (Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom G G n e).relativeAnnihilator hi).symm.trans
    (hr.trans hi)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.KernelParameter.Construction
