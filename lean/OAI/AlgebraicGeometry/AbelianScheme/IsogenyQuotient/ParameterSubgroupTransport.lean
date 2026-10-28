import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupChoice
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TupleImages

/-! # Parameter Subgroup Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterSubgroupTransport.Construction

noncomputable section

section

/-! Actual parameter pullback commutes with images and inverse images
of relative subgroups along the original group-scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} (G H : Grp (Over S)) (P : Over S) (f : H ⟶ G)

set_option backward.isDefEq.respectTransparency false in
theorem relativeSubgroupOverParameter_pullback (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter H P (SubgroupTransport.Construction.relativeSubgroupPullback f.hom.hom F) =
      SubgroupTransport.Construction.relativeSubgroupPullback ((Over.pullback P.hom).map f.hom.hom)
        (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) := by
  ext U t x
  exact Iff.of_eq (congrArg
    (fun z => z ∈ F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U))
    (CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom f U x).symm)

set_option backward.isDefEq.respectTransparency false in
theorem relativeSubgroupOverParameter_image (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup H.X P) :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (SubgroupTransport.Construction.relativeSubgroupImage f.hom.hom F) =
      SubgroupTransport.Construction.relativeSubgroupImage ((Over.pullback P.hom).map f.hom.hom)
        (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter H P F) := by
  ext U t x
  let eG := CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U
  let eH := CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨eH z, ?_, ?_⟩
    · change eH.symm (eH z) ∈ F.points ((Over.map P.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint P U)
      exact (eH.symm_apply_apply z).symm ▸ hz
    · apply eG.symm.injective
      exact (CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom f U (eH z)).trans
        ((congrArg (· ≫ f.hom.hom) (eH.symm_apply_apply z)).trans hzx)
  · rintro ⟨y, hy, hyx⟩
    refine ⟨eH.symm y, hy, ?_⟩
    exact (CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom f U y).symm.trans (congrArg eG.symm hyx)

theorem relativeSubgroupImage_pullback_iso
    {S : Scheme.{0}} {A B P : Over S} [GrpObj A] [GrpObj B]
    (f : B ⟶ A) [IsMonHom f] [IsIso f] (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    SubgroupTransport.Construction.relativeSubgroupImage f (SubgroupTransport.Construction.relativeSubgroupPullback f F) = F := by
  apply SubgroupTransport.Construction.relativeSubgroupPullback_image f F
  intro U t x _
  exact ⟨x ≫ inv f, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

theorem relativeSubgroupPullback_comp
    {S : Scheme.{0}} {A B C P : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
    (f : B ⟶ A) [IsMonHom f] (g : C ⟶ B) [IsMonHom g] (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    SubgroupTransport.Construction.relativeSubgroupPullback g (SubgroupTransport.Construction.relativeSubgroupPullback f F) = SubgroupTransport.Construction.relativeSubgroupPullback (g ≫ f) F := by
  ext U t x
  exact Iff.of_eq (congrArg (fun z => z ∈ F.points U t) (Category.assoc x g f))

end

/-! Images and inverse images commute with an actual group isomorphism
and its specified inclusion square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B C P : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (e : C ≅ B) [IsMonHom e.hom] (f : B ⟶ A) [IsMonHom f]
  (g : C ⟶ A) [IsMonHom g] (he : e.hom ≫ f = g)

include he in
theorem relativeSubgroupImage_iso_square (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P) :
    SubgroupTransport.Construction.relativeSubgroupImage g (SubgroupTransport.Construction.relativeSubgroupPullback e.hom F) = SubgroupTransport.Construction.relativeSubgroupImage f F := by
  subst g
  rw [← TupleImages.Construction.relativeSubgroupImage_comp, relativeSubgroupImage_pullback_iso]

include he in
theorem relativeSubgroupPullback_iso_square (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    SubgroupTransport.Construction.relativeSubgroupPullback e.hom (SubgroupTransport.Construction.relativeSubgroupPullback f F) = SubgroupTransport.Construction.relativeSubgroupPullback g F := by
  subst g
  exact relativeSubgroupPullback_comp f e.hom F

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ParameterSubgroupTransport.Construction
