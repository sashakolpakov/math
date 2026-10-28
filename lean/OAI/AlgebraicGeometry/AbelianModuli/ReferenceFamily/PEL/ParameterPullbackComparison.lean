import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.SubgroupFromParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters

/-! # Parameter Pullback Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ParameterPullbackComparison

noncomputable section

/-! Canonical PEL pullback comparisons over a subgroup parameter
retain the projection to the original abelian family and the full
relative subgroup membership on each test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TotalParameters.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T U : Over (Spec (.of K))}

private theorem reassoc_square {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : X ⟶ Z) (e : W ⟶ Z)
    (hb : b ≫ c = d) (ha : a ≫ d = e) : (a ≫ b) ≫ c = e :=
  (Category.assoc a b c).trans ((congrArg (fun f => a ≫ f) hb).trans ha)

private theorem precomp_square {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : X ⟶ Z)
    (h : b ≫ c = d) : (𝟙 W) ≫ ((a ≫ b) ≫ c) = a ≫ d :=
  (Category.id_comp _).trans ((Category.assoc a b c).trans (congrArg (fun f => a ≫ f) h))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELIso.pullbackCongr (A : Objects.PELObject P iota N T) {f g : U ⟶ T} (h : f = g) :
    Objects.PELIso (A.pullback f) (A.pullback g) := by
  cases h
  exact Objects.PELIso.refl _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELIso.pullbackCongr_hom_fst (A : Objects.PELObject P iota N T)
    {f g : U ⟶ T} (h : f = g) :
    (Objects.PELIso.pullbackCongr A h).polarized.abelian.hom.left ≫
      pullback.fst A.polarized.abelian.scheme.hom g.left =
        pullback.fst A.polarized.abelian.scheme.hom f.left := by
  cases h
  exact Category.id_comp _

def parameterTotalMap {R Q : Over T.left} (k : Q ⟶ R) :
    AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T Q ⟶ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter T R := Over.homMk k.left (by
  change k.left ≫ (R.hom ≫ T.hom) = Q.hom ≫ T.hom
  rw [← Category.assoc, k.w])

theorem parameterTotalMap_source {R Q : Over T.left} (k : Q ⟶ R) :
    parameterTotalMap (T := T) k ≫ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T R = AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q :=
  Over.OverMorphism.ext k.w

def pelParameterPullbackIso (A : Objects.PELObject P iota N T) {R Q : Over T.left} (k : Q ⟶ R) :
    Objects.PELIso ((A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T R)).pullback (parameterTotalMap k))
      (A.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T Q)) :=
  (Objects.PELIso.pullbackComp A (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource T R) (parameterTotalMap k)).symm.trans
    (Objects.PELIso.pullbackCongr A (parameterTotalMap_source k))

theorem pelParameterPullbackIso_hom_fst
    (A : Objects.PELObject P iota N T) {R Q : Over T.left} (k : Q ⟶ R) :
    (pelParameterPullbackIso A k).polarized.abelian.hom.left ≫
      pullback.fst A.polarized.abelian.scheme.hom Q.hom =
        pullback.fst (A.polarized.abelian.pullback R.hom).scheme.hom k.left ≫
          pullback.fst A.polarized.abelian.scheme.hom R.hom := by
  change ((A.polarized.abelian.pullbackCompIso R.hom k.left).inv.left ≫
      (Objects.PELIso.pullbackCongr A (parameterTotalMap_source k)).polarized.abelian.hom.left) ≫
        pullback.fst A.polarized.abelian.scheme.hom Q.hom = _
  exact reassoc_square _ _ _ _ _
    (Objects.PELIso.pullbackCongr_hom_fst A (parameterTotalMap_source k))
    (HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv_left_fst A.polarized.abelian R.hom k.left)

def parameterOriginalTestIso {S : Scheme.{0}} {R Q : Over S} (k : Q ⟶ R) (X : Over Q.left) :
    (Over.map R.hom).obj ((Over.map k.left).obj X) ≅ (Over.map Q.hom).obj X :=
  Over.isoMk (Iso.refl X.left) (by
    change (𝟙 X.left) ≫ (X.hom ≫ Q.hom) = (X.hom ≫ k.left) ≫ R.hom
    rw [Category.id_comp, Category.assoc, k.w])

theorem pelParameterPullbackIso_original_point
    (A : Objects.PELObject P iota N T) {R Q : Over T.left} (k : Q ⟶ R)
    (X : Over Q.left)
    (x : X ⟶ ((A.polarized.abelian.pullback R.hom).pullback k.left).scheme) :
    (parameterOriginalTestIso k X).hom ≫
        A.polarized.abelian.baseChangePointsMulEquiv Q.hom X
          (x ≫ (pelParameterPullbackIso A k).polarized.abelian.hom) =
      A.polarized.abelian.baseChangePointsMulEquiv R.hom ((Over.map k.left).obj X)
        ((A.polarized.abelian.pullback R.hom).baseChangePointsMulEquiv k.left X x) := by
  apply Over.OverMorphism.ext
  change (𝟙 X.left) ≫
      ((x.left ≫ (pelParameterPullbackIso A k).polarized.abelian.hom.left) ≫
        pullback.fst A.polarized.abelian.scheme.hom Q.hom) =
    (x.left ≫ pullback.fst (A.polarized.abelian.pullback R.hom).scheme.hom k.left) ≫
      pullback.fst A.polarized.abelian.scheme.hom R.hom
  exact (precomp_square _ _ _ _ (pelParameterPullbackIso_hom_fst A k)).trans
    (Category.assoc _ _ _).symm

theorem pelParameterPullbackIso_subgroup_membership
    (A : Objects.PELObject P iota N T) {R Q : Over T.left} (k : Q ⟶ R)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme R)
    (X : Over Q.left)
    (x : X ⟶ ((A.polarized.abelian.pullback R.hom).pullback k.left).scheme) :
    A.polarized.abelian.baseChangePointsMulEquiv R.hom ((Over.map k.left).obj X)
        ((A.polarized.abelian.pullback R.hom).baseChangePointsMulEquiv k.left X x) ∈
      F.points ((Over.map R.hom).obj ((Over.map k.left).obj X))
        (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint R ((Over.map k.left).obj X)) ↔
    A.polarized.abelian.baseChangePointsMulEquiv Q.hom X
        (x ≫ (pelParameterPullbackIso A k).polarized.abelian.hom) ∈
      (F.baseChange k).points ((Over.map Q.hom).obj X) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q X) := by
  have ht : (parameterOriginalTestIso k X).hom ≫ (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q X ≫ k) =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint R ((Over.map k.left).obj X) := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  rw [← pelParameterPullbackIso_original_point, ← ht]
  exact Relative.SubgroupFromParameter.relativeSubgroup_membership_iso F (parameterOriginalTestIso k X)
    (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint Q X ≫ k) _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ParameterPullbackComparison
