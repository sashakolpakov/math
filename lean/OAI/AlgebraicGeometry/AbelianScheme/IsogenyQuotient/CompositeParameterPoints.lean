import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELCompositeSource
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints

/-! # Composite Parameter Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompositeParameterPoints.Construction

noncomputable section

section

/-! Original points and subgroup membership are coherent through the
two base changes in an actual source-fiber specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def compositeBaseTestIso {S S' S'' : Scheme.{0}}
    (f : S' ⟶ S) (h : S'' ⟶ S') (g : S'' ⟶ S) (hg : h ≫ f = g) (U : Over S'') :
    (Over.map f).obj ((Over.map h).obj U) ≅ (Over.map g).obj U :=
  Over.isoMk (Iso.refl _) ((Category.id_comp (U.hom ≫ g)).trans
    ((congrArg (U.hom ≫ ·) hg.symm).trans (Category.assoc U.hom h f).symm))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T V W : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)

set_option backward.isDefEq.respectTransparency false in
theorem pelCompositeSourceIso_original_points (f : V ⟶ T) (h : W ⟶ V) (g : W ⟶ T) (hg : h ≫ f = g)
    (U : Over W.left) (z : U ⟶ (A.pullback g).polarized.abelian.scheme) :
    A.polarized.abelian.baseChangePointsMulEquiv f.left ((Over.map h.left).obj U)
      ((A.polarized.abelian.pullback f.left).baseChangePointsMulEquiv h.left U
        (z ≫ (PELCompositeSource.Construction.pelCompositeSourceIso A f h g hg).polarized.abelian.hom)) =
      (compositeBaseTestIso f.left h.left g.left (congrArg Over.Hom.left hg) U).hom ≫
        A.polarized.abelian.baseChangePointsMulEquiv g.left U z := by
  apply Over.OverMorphism.ext
  change ((z.left ≫ (PELCompositeSource.Construction.pelCompositeSourceIso A f h g hg).polarized.abelian.hom.left) ≫
      pullback.fst (A.polarized.abelian.pullback f.left).scheme.hom h.left) ≫
        pullback.fst A.polarized.abelian.scheme.hom f.left =
    (𝟙 U.left) ≫ (z.left ≫ pullback.fst A.polarized.abelian.scheme.hom g.left)
  simp only [Category.assoc, Category.id_comp]
  exact congrArg (z.left ≫ ·) (PELCompositeSource.Construction.pelCompositeSourceIso_original_point A f h g hg)

variable (Q : Over T.left) (y : V ⟶ TotalParameters.Construction.totalParameter T Q) (x : V ⟶ T)
  (hy : y ≫ TotalParameters.Construction.totalParameterSource T Q = x)

theorem sourceFiberParameterPoint_composite (U : Over V.left) :
    (compositeBaseTestIso Q.hom y.left x.left (congrArg Over.Hom.left hy) U).hom ≫
      (Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk x.left) U ≫ (TotalParameters.Construction.totalParameterFiberLiftEquiv T Q V x ⟨y, hy⟩)) =
        Relative.ParameterBaseChange.Construction.parameterBasePoint Q ((Over.map y.left).obj U) := by
  apply Over.OverMorphism.ext
  change (𝟙 U.left) ≫ (U.hom ≫ y.left) = U.hom ≫ y.left
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
theorem compositePELParameterPoint_membership
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme Q) (U : Over V.left)
    (z : U ⟶ (A.pullback x).polarized.abelian.scheme) :
    A.polarized.abelian.baseChangePointsMulEquiv Q.hom ((Over.map y.left).obj U)
      ((A.polarized.abelian.pullback Q.hom).baseChangePointsMulEquiv y.left U
        (z ≫ (PELCompositeSource.Construction.pelCompositeSourceIso A (TotalParameters.Construction.totalParameterSource T Q) y x hy).polarized.abelian.hom)) ∈
      F.points ((Over.map Q.hom).obj ((Over.map y.left).obj U))
        (Relative.ParameterBaseChange.Construction.parameterBasePoint Q ((Over.map y.left).obj U)) ↔
    A.polarized.abelian.baseChangePointsMulEquiv x.left U z ∈
      (F.baseChange (TotalParameters.Construction.totalParameterFiberLiftEquiv T Q V x ⟨y, hy⟩)).points
        ((Over.map x.left).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk x.left) U) := by
  have hp := pelCompositeSourceIso_original_points A (TotalParameters.Construction.totalParameterSource T Q) y x hy U z
  have hb := sourceFiberParameterPoint_composite Q y x hy U
  have hm := Parameter.TestComparison.Construction.relativeSubgroup_membership_iso F
    (compositeBaseTestIso Q.hom y.left x.left (congrArg Over.Hom.left hy) U)
    (Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk x.left) U ≫ TotalParameters.Construction.totalParameterFiberLiftEquiv T Q V x ⟨y, hy⟩)
    (A.polarized.abelian.baseChangePointsMulEquiv x.left U z)
  exact hp.symm ▸ (hb ▸ hm)

end

/-! The quotient specialized at a source-fiber point has the actual
parameter pullback of its universal kernel on the original source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T V : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T)
  (Q : Over T.left) (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme Q) (R : F.Model)
  {B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (TotalParameters.Construction.totalParameter T Q)}
  (r : Intrinsic.PELBaseChange.Construction.NativePELQuotient (A.pullback (TotalParameters.Construction.totalParameterSource T Q)) B n)
  (hker : ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left)
    (z : U ⟶ (A.polarized.abelian.pullback Q.hom).scheme),
    z ≫ r.isogeny.hom = 1 ↔ ∃! w : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
      w ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A.polarized.abelian Q F R = z)
  (y : V ⟶ TotalParameters.Construction.totalParameter T Q) (x : V ⟶ T) (hy : y ≫ TotalParameters.Construction.totalParameterSource T Q = x)

include hker in
set_option backward.isDefEq.respectTransparency false in
theorem sourceFiberQuotient_kernel (U : Over V.left)
    (z : U ⟶ (A.pullback x).polarized.abelian.scheme)
    (t : U ⟶ Over.mk (𝟙 V.left)) :
    z ≫ (r.pullbackCompositeSource A (TotalParameters.Construction.totalParameterSource T Q) y x hy).isogeny.hom = 1 ↔
      z ∈ (Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.polarized.abelian.scheme) (Over.mk x.left)
        (F.baseChange (TotalParameters.Construction.totalParameterFiberLiftEquiv T Q V x ⟨y, hy⟩))).points U t := by
  rw [Intrinsic.PELBaseChange.Construction.NativePELQuotient.pullbackCompositeSource_hom, ← Category.assoc]
  exact (Intrinsic.KernelPoints.Construction.nativeQuotient_pullback_kernel_membership A.polarized.abelian Q F R r.isogeny hker y.left U
    (z ≫ (PELCompositeSource.Construction.pelCompositeSourceIso A (TotalParameters.Construction.totalParameterSource T Q) y x hy).polarized.abelian.hom)).trans
      (compositePELParameterPoint_membership A Q y x hy F U z)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompositeParameterPoints.Construction
