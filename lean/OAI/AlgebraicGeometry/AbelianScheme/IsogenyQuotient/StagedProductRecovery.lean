import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedRecovery
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Staged Product Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedProductRecovery.Construction

noncomputable section

section

/-! Simultaneous product recovery is the actual parameter-family
isomorphism, with explicit projections to its base and original product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

variable {S Y : Scheme.{0}} (u : Y ⟶ S) (E B : Over S)

def productFamilyParameterIso :
    (((Over.pullback u).obj E) ⊗ ((Over.pullback u).obj B)).left ≅
      (Over.mk u ⊗ (E ⊗ B)).left :=
  (Over.forget Y).mapIso (Functor.Monoidal.μIso (Over.pullback u) E B) ≪≫
    pullbackSymmetry (E ⊗ B).hom u

theorem productFamilyParameterIso_fst :
    (productFamilyParameterIso u E B).hom ≫ (fst (Over.mk u) (E ⊗ B)).left =
      (((Over.pullback u).obj E) ⊗ ((Over.pullback u).obj B)).hom := by
  change ((Functor.Monoidal.μIso (Over.pullback u) E B).hom.left ≫
    (pullbackSymmetry (E ⊗ B).hom u).hom) ≫ pullback.fst u (E ⊗ B).hom = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact (Functor.Monoidal.μIso (Over.pullback u) E B).hom.w

theorem productFamilyParameterIso_snd :
    (productFamilyParameterIso u E B).hom ≫ (snd (Over.mk u) (E ⊗ B)).left =
      (Functor.Monoidal.μIso (Over.pullback u) E B).hom.left ≫ pullback.fst (E ⊗ B).hom u := by
  change ((Functor.Monoidal.μIso (Over.pullback u) E B).hom.left ≫
    (pullbackSymmetry (E ⊗ B).hom u).hom) ≫ pullback.snd u (E ⊗ B).hom = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]

variable {D A : Over Y} (eD : D ≅ (Over.pullback u).obj E) (eA : A ≅ (Over.pullback u).obj B)

def recoveredProductParameterIso : (D ⊗ A).left ≅ (Over.mk u ⊗ (E ⊗ B)).left :=
  (Over.forget Y).mapIso (tensorIso eD eA) ≪≫ productFamilyParameterIso u E B

theorem recoveredProductParameterIso_fst :
    (recoveredProductParameterIso u E B eD eA).hom ≫ (fst (Over.mk u) (E ⊗ B)).left =
      (D ⊗ A).hom := by
  change ((tensorIso eD eA).hom.left ≫ (productFamilyParameterIso u E B).hom) ≫ _ = _
  rw [Category.assoc, productFamilyParameterIso_fst]
  exact (tensorIso eD eA).hom.w

theorem recoveredProductParameterIso_snd :
    (recoveredProductParameterIso u E B eD eA).hom ≫ (snd (Over.mk u) (E ⊗ B)).left =
      AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD eA := by
  change ((tensorIso eD eA).hom.left ≫ (productFamilyParameterIso u E B).hom) ≫ _ = _
  rw [Category.assoc, productFamilyParameterIso_snd]
  exact (Category.assoc _ _ _).symm

end

section

/-! The Poincare parameter line and the two recovered abelian schemes
have the same simultaneous product map after a base enlargement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

theorem productFamilyParameterIso_snd_fst
    {S T : Scheme.{0}} (v : T ⟶ S) (E B : Over S) :
    (productFamilyParameterIso v E B).hom ≫ (snd (Over.mk v) (E ⊗ B)).left ≫ (fst E B).left =
      (fst ((Over.pullback v).obj E) ((Over.pullback v).obj B)).left ≫ pullback.fst E.hom v := by
  rw [← Category.assoc, productFamilyParameterIso_snd, Category.assoc]
  exact Over.μ_pullback_left_fst_fst E B

theorem productFamilyParameterIso_snd_snd
    {S T : Scheme.{0}} (v : T ⟶ S) (E B : Over S) :
    (productFamilyParameterIso v E B).hom ≫ (snd (Over.mk v) (E ⊗ B)).left ≫ (snd E B).left =
      (snd ((Over.pullback v).obj E) ((Over.pullback v).obj B)).left ≫ pullback.fst B.hom v := by
  rw [← Category.assoc, productFamilyParameterIso_snd, Category.assoc]
  exact Over.μ_pullback_left_fst_snd E B

set_option backward.isDefEq.respectTransparency false in
theorem stagedProductRecovery_square
    {S T Y : Scheme.{0}} {g h : ℕ}
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y) (D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h Y)
    (v : T ⟶ S) (u : Y ⟶ T) (w : Y ⟶ S) (hu : u ≫ v = w)
    (eA : A.scheme ≅ (B.pullback w).scheme) (eD : D.scheme ≅ (E.pullback w).scheme) :
    AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u
        (StagedRecovery.Construction.stagedAbelianRecovery E D v u w hu eD) (StagedRecovery.Construction.stagedAbelianRecovery B A v u w hu eA) ≫
      (productFamilyParameterIso v E.scheme B.scheme).hom =
    (recoveredProductParameterIso w E.scheme B.scheme eD eA).hom ≫
      ((Over.homMk u hu : Over.mk w ⟶ Over.mk v) ▷ (E.scheme ⊗ B.scheme)).left := by
  let eD₀ : D.scheme ≅ (Over.pullback w).obj E.scheme := eD
  let eA₀ : A.scheme ≅ (Over.pullback w).obj B.scheme := eA
  let eD' : D.scheme ≅ (Over.pullback u).obj ((Over.pullback v).obj E.scheme) :=
    StagedRecovery.Construction.stagedAbelianRecovery E D v u w hu eD
  let eA' : A.scheme ≅ (Over.pullback u).obj ((Over.pullback v).obj B.scheme) :=
    StagedRecovery.Construction.stagedAbelianRecovery B A v u w hu eA
  let q : Over.mk w ⟶ Over.mk v := Over.homMk u hu
  let c := recoveredProductParameterIso w E.scheme B.scheme eD₀ eA₀
  let d := productFamilyParameterIso v E.scheme B.scheme
  let m : (D.scheme ⊗ A.scheme).left ⟶
      (((Over.pullback v).obj E.scheme) ⊗ ((Over.pullback v).obj B.scheme)).left :=
    AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u eD' eA'
  change m ≫ d.hom = c.hom ≫ (q ▷ (E.scheme ⊗ B.scheme)).left
  apply Over.tensorObj_ext
  · change (m ≫ d.hom) ≫ (fst (Over.mk v) (E.scheme ⊗ B.scheme)).left =
      (c.hom ≫ (q ▷ (E.scheme ⊗ B.scheme)).left) ≫
        (fst (Over.mk v) (E.scheme ⊗ B.scheme)).left
    rw [Category.assoc, productFamilyParameterIso_fst]
    have hq : (q ▷ (E.scheme ⊗ B.scheme)).left ≫
        (fst (Over.mk v) (E.scheme ⊗ B.scheme)).left =
      (fst (Over.mk w) (E.scheme ⊗ B.scheme)).left ≫ u :=
      Over.whiskerRight_left_fst q
    rw [Category.assoc, hq, ← Category.assoc, recoveredProductParameterIso_fst]
    exact (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap_isPullback u eD' eA').w.symm
  · change (m ≫ d.hom) ≫ (snd (Over.mk v) (E.scheme ⊗ B.scheme)).left =
      (c.hom ≫ (q ▷ (E.scheme ⊗ B.scheme)).left) ≫
        (snd (Over.mk v) (E.scheme ⊗ B.scheme)).left
    have hq : (q ▷ (E.scheme ⊗ B.scheme)).left ≫
        (snd (Over.mk v) (E.scheme ⊗ B.scheme)).left =
      (snd (Over.mk w) (E.scheme ⊗ B.scheme)).left :=
      Over.whiskerRight_left_snd q
    rw [Category.assoc, Category.assoc, hq, recoveredProductParameterIso_snd]
    apply Over.tensorObj_ext
    · change ((m ≫ d.hom) ≫ (snd (Over.mk v) (E.scheme ⊗ B.scheme)).left) ≫
        (fst E.scheme B.scheme).left = AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap w eD₀ eA₀ ≫ (fst E.scheme B.scheme).left
      rw [Category.assoc, Category.assoc, productFamilyParameterIso_snd_fst,
        ← Category.assoc, AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap_fst, Category.assoc]
      exact (congrArg (fun z => (fst D.scheme A.scheme).left ≫ z)
        (StagedRecovery.Construction.stagedAbelianRecovery_totalMap_comp E D v u w hu eD)).trans
          (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap_fst w eD₀ eA₀).symm
    · change ((m ≫ d.hom) ≫ (snd (Over.mk v) (E.scheme ⊗ B.scheme)).left) ≫
        (snd E.scheme B.scheme).left = AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap w eD₀ eA₀ ≫ (snd E.scheme B.scheme).left
      rw [Category.assoc, Category.assoc, productFamilyParameterIso_snd_snd,
        ← Category.assoc, AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap_snd, Category.assoc]
      exact (congrArg (fun z => (snd D.scheme A.scheme).left ≫ z)
        (StagedRecovery.Construction.stagedAbelianRecovery_totalMap_comp B A v u w hu eA)).trans
          (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap_snd w eD₀ eA₀).symm

end

/-! Enlarging the base of a full dual model retains the recovered
original Poincare class through the canonical native dual pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

set_option backward.isDefEq.respectTransparency false in
theorem stagedPoincareRecovery_map
    {S T Y : Scheme.{0}} {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (v : T ⟶ S) (u : Y ⟶ T) (w : Y ⟶ S) (hu : u ≫ v = w)
    (eA : A.scheme ≅ (B.pullback w).scheme) (eD : D.abelian.scheme ≅ (E.abelian.pullback w).scheme) :
    AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u (StagedRecovery.Construction.stagedAbelianRecovery E.abelian D.abelian v u w hu eD)
        (StagedRecovery.Construction.stagedAbelianRecovery B A v u w hu eA) ≫ (E.poincarePullbackOverMap v).left =
      AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap w eD eA := by
  have hs := congrArg (fun f => f ≫ (snd (Over.mk v) (E.abelian.scheme ⊗ B.scheme)).left)
    (stagedProductRecovery_square B E.abelian A D.abelian v u w hu eA eD)
  have hq : ((Over.homMk u hu : Over.mk w ⟶ Over.mk v) ▷ (E.abelian.scheme ⊗ B.scheme)).left ≫
      (snd (Over.mk v) (E.abelian.scheme ⊗ B.scheme)).left =
        (snd (Over.mk w) (E.abelian.scheme ⊗ B.scheme)).left :=
    Over.whiskerRight_left_snd (R := E.abelian.scheme ⊗ B.scheme)
      (Over.homMk u hu : Over.mk w ⟶ Over.mk v)
  rw [Category.assoc, productFamilyParameterIso_snd, Category.assoc, hq,
    recoveredProductParameterIso_snd] at hs
  rw [← AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
  exact hs

theorem stagedPoincareRecovery_class
    {S T Y : Scheme.{0}} {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (v : T ⟶ S) (u : Y ⟶ T) (w : Y ⟶ S) (hu : u ≫ v = w)
    (eA : A.scheme ≅ (B.pullback w).scheme) (eD : D.abelian.scheme ≅ (E.abelian.pullback w).scheme)
    (hP : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap w eD eA)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (AbelianModuli.ReferenceFamily.CartesianMixedProduct.CartesianFamily.mixedMap u (StagedRecovery.Construction.stagedAbelianRecovery E.abelian D.abelian v u w hu eD)
        (StagedRecovery.Construction.stagedAbelianRecovery B A v u w hu eA))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (E.pullback v).poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (E.poincarePullbackOverMap v).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, stagedPoincareRecovery_map]
  exact hP

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.StagedProductRecovery.Construction
