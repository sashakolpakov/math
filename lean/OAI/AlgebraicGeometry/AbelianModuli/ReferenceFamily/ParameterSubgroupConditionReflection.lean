import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.SubgroupFromParameterModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.KernelParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterSubgroupTransport

/-! # Parameter Subgroup Condition Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterSubgroupConditionReflection

noncomputable section

/-! Passage to a parameter scheme reflects the original stability
and self-annihilator conditions. Finite subgroup choices can therefore
be recovered on the original abelian family without a chosen marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

attribute [local instance] AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative

def subgroupChoiceFromParameter {S : Scheme.{0}} (G : Grp (Over S)) (P : Over S)
    (n : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice ((Over.pullback P.hom).obj G.X) n M (Over.mk (𝟙 P.left))) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice G.X n M P where
  subgroup := Relative.SubgroupFromParameter.relativeSubgroupFromParameter G P F.subgroup
  killed := Relative.SubgroupFromParameter.relativeSubgroupFromParameter_killed G P F.subgroup n F.killed
  moduleType := Relative.SubgroupFromParameter.relativeSubgroupFromParameter_moduleType G P F.subgroup M F.moduleType
  geometric := F.geometric.elim fun R => ⟨Relative.SubgroupFromParameterModel.relativeSubgroupFromParameterModel G P F.subgroup R⟩

theorem relativeSubgroupFromParameter_stable
    {S : Scheme.{0}} (G : Grp (Over S)) (P : Over S)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).obj G.X) (Over.mk (𝟙 P.left)))
    (a : G ⟶ G) (h : AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F ((Over.pullback P.hom).map a.hom.hom)) :
    AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable (Relative.SubgroupFromParameter.relativeSubgroupFromParameter G P F) a.hom.hom := by
  intro X t x hx
  change ParameterPointTransport.parameterPointMulEquiv G P X t (x ≫ a.hom.hom) ∈
    F.points (Over.mk t.left) (Relative.SubgroupFromParameter.terminalParameterPoint (Over.mk t.left))
  rw [ParameterPointTransport.parameterPointMulEquiv_comp]
  exact h _ _ _ hx

theorem relativeSubgroupPullback_iso_injective
    {S : Scheme.{0}} {A B P : Over S} [GrpObj A] [GrpObj B]
    (f : B ⟶ A) [IsMonHom f] [IsIso f] :
    Function.Injective (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (P := P) f) := by
  intro F H h
  exact (AbelianScheme.IsogenyQuotient.ParameterSubgroupTransport.Construction.relativeSubgroupImage_pullback_iso f F).symm.trans
    ((congrArg (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage f) h).trans (AbelianScheme.IsogenyQuotient.ParameterSubgroupTransport.Construction.relativeSubgroupImage_pullback_iso f H))

theorem nativeTorsionSubgroupOverParameter_self_annihilating_iff
    {S : Scheme.{0}} (G : Grp (Over S)) [IsCommMonObj G.X] (P : Over S)
    (n : ℕ) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P)
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n) (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme G.X n)
      (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X)) :
    (let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
        (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n)
        (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F)
     (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom G G n e).relativeAnnihilator H = H) ↔
      e.relativeAnnihilator (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n) F) =
        AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion G.X n) F := by
  constructor
  · intro h
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionInclusion G n).hom.hom F
    let HP := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) P H
    let ep := AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.nativePairingPullback P.hom (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) e
    let i := (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso P.hom G n).inv.hom.hom
    apply AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.relativeSubgroupOverParameter_injective (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) P
    refine (AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison.Construction.relativeParameter_annihilator_comparison
      (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) (AbelianScheme.IsogenyQuotient.Torsion.SheafComparison.Construction.kernelTorsionGroup G n) P H e).trans ?_
    apply relativeSubgroupPullback_iso_injective i
    have hi := AbelianScheme.IsogenyQuotient.Torsion.KernelParameter.Construction.nativeTorsionSubgroupOverParameter_comparison G P n F
    have hr := ep.restrict_annihilator_iso i i HP
    calc
      AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i (ep.relativeAnnihilator HP) =
          (ep.restrict i i).relativeAnnihilator (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i HP) := hr.symm
      _ = (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom G G n e).relativeAnnihilator
          (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
            (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n)
            (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F)) :=
        congrArg (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom G G n e).relativeAnnihilator hi
      _ = AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
          (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n)
          (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) := h
      _ = AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i HP := hi.symm
  · exact AbelianScheme.IsogenyQuotient.Torsion.KernelParameter.Construction.nativeTorsionSubgroupOverParameter_self_annihilating G P n F e

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterSubgroupConditionReflection
