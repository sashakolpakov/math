import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCompositeSource
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.ComplexTarget
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison

/-! # Identity PEL -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IdentityPEL.Construction

/-! Remove the two identity pullbacks in the independent relative
quotient. The full PEL comparison is the identity on original points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem identityTotalParameterPoint_source {S : Scheme.{0}} (T : Over S) :
    Reference.ComplexTarget.Construction.identityTotalParameterPoint T ≫ TotalParameters.Construction.totalParameterSource T (Over.mk (𝟙 T.left)) = 𝟙 T :=
  Over.OverMorphism.ext (Category.id_comp _)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)

def identityParameterPELSourceIso : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A
    ((PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T (Over.mk (𝟙 T.left)))).pullback (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)) :=
  (AbelianModuli.ReferenceFamily.PEL.Objects.PELIso.pullbackId A).symm.trans
    (PELCompositeSource.Construction.pelCompositeSourceIso A (TotalParameters.Construction.totalParameterSource T (Over.mk (𝟙 T.left))) (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)
      (𝟙 T) (identityTotalParameterPoint_source T))

set_option backward.isDefEq.respectTransparency false in
theorem identityParameterPELSourceIso_original_point :
    (identityParameterPELSourceIso A).polarized.abelian.hom.left ≫
      pullback.fst (A.polarized.abelian.pullback (𝟙 T.left)).scheme.hom (𝟙 T.left) ≫
        pullback.fst A.polarized.abelian.scheme.hom (𝟙 T.left) = 𝟙 A.polarized.abelian.scheme.left := by
  let e := PELCompositeSource.Construction.pelCompositeSourceIso A (TotalParameters.Construction.totalParameterSource T (Over.mk (𝟙 T.left))) (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)
    (𝟙 T) (identityTotalParameterPoint_source T)
  have he : e.polarized.abelian.hom.left ≫
      pullback.fst (A.polarized.abelian.pullback (𝟙 T.left)).scheme.hom (𝟙 T.left) ≫
        pullback.fst A.polarized.abelian.scheme.hom (𝟙 T.left) =
      pullback.fst A.polarized.abelian.scheme.hom (𝟙 T.left) :=
    PELCompositeSource.Construction.pelCompositeSourceIso_original_point A (TotalParameters.Construction.totalParameterSource T (Over.mk (𝟙 T.left)))
      (Reference.ComplexTarget.Construction.identityTotalParameterPoint T) (𝟙 T) (identityTotalParameterPoint_source T)
  have hi : A.polarized.abelian.pullbackIdIso.inv.left ≫
      pullback.fst A.polarized.abelian.scheme.hom (𝟙 T.left) = 𝟙 _ := by
    rw [← A.polarized.abelian.pullbackIdIso_hom_left]
    exact ((Over.forget T.left).mapIso A.polarized.abelian.pullbackIdIso).inv_hom_id
  change (A.polarized.abelian.pullbackIdIso.inv.left ≫ e.polarized.abelian.hom.left) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (A.polarized.abelian.pullbackIdIso.inv.left ≫ ·) he).trans hi)

end AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IdentityPEL.Construction

namespace AlgebraicGeometry.AbelianScheme.IsogenyQuotient

/-! The independently constructed relative quotient over the identity
parameter is an actual quotient of the original PEL object. Its kernel
is the original subgroup on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} {A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T}
  {F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme (Over.mk (𝟙 T.left))}

def Noetherian.RelativePEL.Construction.RelativePELQuotient.identityQuotient (H : Noetherian.RelativePEL.Construction.RelativePELQuotient A (Over.mk (𝟙 T.left)) F n) :
    Intrinsic.PELBaseChange.Construction.NativePELQuotient A (H.object.pullback (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)) n :=
  (H.quotient.pullback (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)).precompose (IdentityPEL.Construction.identityParameterPELSourceIso A)

set_option backward.isDefEq.respectTransparency false in
theorem Noetherian.RelativePEL.Construction.RelativePELQuotient.identityQuotient_kernel
    (H : Noetherian.RelativePEL.Construction.RelativePELQuotient A (Over.mk (𝟙 T.left)) F n)
    (U : Over T.left) (a : U ⟶ A.polarized.abelian.scheme) :
    a ≫ H.identityQuotient.isogeny.hom = 1 ↔
      a ∈ F.points U (Over.homMk U.hom (Category.comp_id U.hom)) := by
  let e := IdentityPEL.Construction.identityParameterPELSourceIso A
  let U' := (Over.map (𝟙 T.left)).obj ((Over.map (𝟙 T.left)).obj U)
  let t : U ⟶ Over.mk (𝟙 T.left) := Over.homMk U.hom (Category.comp_id _)
  let t' := Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk (𝟙 T.left)) ((Over.map (𝟙 T.left)).obj U)
  let a' := A.polarized.abelian.baseChangePointsMulEquiv (𝟙 T.left) ((Over.map (𝟙 T.left)).obj U)
    ((A.polarized.abelian.pullback (𝟙 T.left)).baseChangePointsMulEquiv (𝟙 T.left) U (a ≫ e.polarized.abelian.hom))
  let i : U' ≅ U := Over.isoMk (Iso.refl _) (by
    change (𝟙 U.left) ≫ U.hom = (U.hom ≫ 𝟙 T.left) ≫ 𝟙 T.left
    simp only [Category.id_comp, Category.comp_id])
  have ht : i.hom ≫ t = t' := by
    apply Over.OverMorphism.ext
    change (𝟙 U.left) ≫ U.hom = U.hom ≫ 𝟙 T.left
    simp only [Category.id_comp, Category.comp_id]
  have ha : i.hom ≫ a = a' := by
    apply Over.OverMorphism.ext
    change (𝟙 U.left) ≫ a.left =
      ((a.left ≫ e.polarized.abelian.hom.left) ≫
        pullback.fst (A.polarized.abelian.pullback (𝟙 T.left)).scheme.hom (𝟙 T.left)) ≫
          pullback.fst A.polarized.abelian.scheme.hom (𝟙 T.left)
    have hh := congrArg (a.left ≫ ·) (IdentityPEL.Construction.identityParameterPELSourceIso_original_point A)
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using hh.symm
  have hm : a' ∈ F.points U' t' ↔ a ∈ F.points U t := by
    simpa only [ht, ha] using Parameter.TestComparison.Construction.relativeSubgroup_membership_iso F i t a
  have hk : a ≫ H.identityQuotient.isogeny.hom = 1 ↔ a' ∈ F.points U' t' :=
    ((H.quotient.pullback (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)).precompose_kernel e U a).trans
      ((Intrinsic.KernelPoints.Construction.isogeny_pullback_kernel_membership H.quotient.isogeny (𝟙 T.left) U (a ≫ e.polarized.abelian.hom)).trans
        (H.kernel ((Over.map (𝟙 T.left)).obj U) _))
  exact hk.trans hm

theorem Noetherian.RelativePEL.Construction.RelativePELQuotient.identityQuotient_classifies
    (H : Noetherian.RelativePEL.Construction.RelativePELQuotient A (Over.mk (𝟙 T.left)) F n)
    (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine) :
    FinePELTarget.Construction.finePELClassifyingMap Z hZ (H.object.pullback (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)) =
      Reference.ComplexTarget.Construction.identityTotalParameterPoint T ≫ H.target Z hZ :=
  FinePELPolarization.Construction.finePELClassifyingMap_pullback Z hZ H.object (Reference.ComplexTarget.Construction.identityTotalParameterPoint T)

end AlgebraicGeometry.AbelianScheme.IsogenyQuotient

end

end OAI
