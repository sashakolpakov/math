import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy

/-! # Kernel Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelBaseChange.Construction

noncomputable section

/-!
The actual scheme-morphism kernel and its self-annihilation specialize
through every base map. The source pairing and the ambient torsion are
transported by their canonical native comparisons.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative TorsionBaseChange.Construction.nativeTorsionPullback_commutative

variable {S : Scheme.{u}} (G H : Grp (Over S)) (P : Over S) (f : G ⟶ H)

theorem nativeMorphismKernel_baseChange :
    MorphismKernel.Construction.nativeMorphismKernel ((Over.pullback P.hom).mapGrp.map f).hom.hom =
      Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P ((MorphismKernel.Construction.nativeMorphismKernel f.hom.hom).baseChange
        (Over.homMk P.hom (Category.comp_id P.hom))) := by
  ext U t x
  change x ≫ ((Over.pullback P.hom).mapGrp.map f).hom.hom = 1 ↔
    (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x ≫ f.hom.hom = 1
  have hn := CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom f U x
  constructor
  · intro hx
    exact hn.symm.trans ((congrArg (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U).symm hx).trans
      (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U).symm.map_one)
  · intro hx
    apply (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U).symm.injective
    exact hn.trans (hx.trans (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U).symm.map_one.symm)

variable [IsCommMonObj G.X]

theorem nativeMorphismKernel_self_annihilating_baseChange (n : ℕ)
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme G.X n) (B := Torsion.Groups.Construction.nativeTorsionScheme G.X n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (h : e.relativeAnnihilator
        (SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion G.X n) (MorphismKernel.Construction.nativeMorphismKernel f.hom.hom)) =
      SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion G.X n) (MorphismKernel.Construction.nativeMorphismKernel f.hom.hom)) :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n)
      (MorphismKernel.Construction.nativeMorphismKernel ((Over.pullback P.hom).mapGrp.map f).hom.hom)
    (TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom G G n e).relativeAnnihilator F = F := by
  let c : P ⟶ Over.mk (𝟙 S) := Over.homMk P.hom (Category.comp_id P.hom)
  let F := (MorphismKernel.Construction.nativeMorphismKernel f.hom.hom).baseChange c
  have hF : e.relativeAnnihilator (SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion G.X n) F) =
      SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion G.X n) F := by
    have hc := congrArg (fun R : TorsionQuotient.SubgroupFunctor.RelativeSubgroup (Torsion.Groups.Construction.nativeTorsionScheme G.X n) (Over.mk (𝟙 S)) =>
      R.baseChange c) h
    rw [e.relativeAnnihilator_baseChange, SubgroupTransport.Construction.relativeSubgroupPullback_baseChange] at hc
    exact hc
  have hi := congrArg
    (SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback P.hom).mapGrp.obj G).X n))
    (nativeMorphismKernel_baseChange G H P f)
  exact (congrArg (TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom G G n e).relativeAnnihilator hi).trans
    ((Torsion.KernelParameter.Construction.nativeTorsionSubgroupOverParameter_self_annihilating G P n F e hF).trans hi.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelBaseChange.Construction
