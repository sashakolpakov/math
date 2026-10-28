import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientClassifyingCharts

/-! # Quotient Classifying Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian

noncomputable section

/-!
An actual finite projective quotient of a finite free module determines a
morphism from the coefficient spectrum to the constructed Grassmannian.
The morphism is obtained by gluing its normalized principal charts.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u}) (N : Module.Grassmannian R (ν → R) (Fintype.card ι))

def quotientPrincipalCover : (Spec R).AffineOpenCover where
  I₀ := PrimeSpectrum R
  X p := CommRingCat.of (Localization.Away (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.denominator)
  f p := (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.scheme.hom
  idx x := x
  covers x := by
    change x ∈ (Spec.map (CommRingCat.ofHom (algebraMap R
      (Localization.Away (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N x).val.denominator)))).opensRange
    rw [Scheme.Hom.opensRange_localizationAway]
    exact (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N x).property
  map_prop p := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R
      (Localization.Away (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.denominator))))
    infer_instance

theorem quotientPrincipalClassifyingMaps_glue (p q : PrimeSpectrum R) :
    pullback.fst ((quotientPrincipalCover R N).f p) ((quotientPrincipalCover R N).f q) ≫
        (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.classifyingMap.left =
      pullback.snd ((quotientPrincipalCover R N).f p) ((quotientPrincipalCover R N).f q) ≫
        (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N q).val.classifyingMap.left := by
  let D := (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val
  let E := (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N q).val
  let T : Over (Spec R) := Over.mk (pullback.fst D.scheme.hom E.scheme.hom ≫ D.scheme.hom)
  let f : T ⟶ D.scheme := Over.homMk (pullback.fst D.scheme.hom E.scheme.hom)
  let g : T ⟶ E.scheme := Over.homMk (pullback.snd D.scheme.hom E.scheme.hom) pullback.condition.symm
  exact congrArg Over.Hom.left (D.classifyingMaps_agree E f g)

def quotientClassifyingMap : Spec R ⟶ Presentations.Grassmannian.Gluing.grassmannianScheme (ι := ι) (ν := ν) (Spec R) :=
  (quotientPrincipalCover R N).openCover.glueMorphisms
    (fun p => (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.classifyingMap.left)
    (quotientPrincipalClassifyingMaps_glue R N)

theorem quotientClassifyingMap_chart (p : PrimeSpectrum R) :
    (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.scheme.hom ≫ quotientClassifyingMap R N =
      (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.classifyingMap.left :=
  (quotientPrincipalCover R N).openCover.ι_glueMorphisms _ _ p

theorem quotientClassifyingMap_over :
    quotientClassifyingMap R N ≫ Presentations.Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R) = 𝟙 (Spec R) := by
  apply (quotientPrincipalCover R N).openCover.hom_ext
  intro p
  change PrimeSpectrum R at p
  change (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.scheme.hom ≫
      (quotientClassifyingMap R N ≫ Presentations.Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := ν) (Spec R)) =
    (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.scheme.hom ≫ 𝟙 (Spec R)
  rw [← Category.assoc, quotientClassifyingMap_chart, Category.comp_id]
  exact (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val.classifyingMap.w

def quotientClassifyingOver : Over.mk (𝟙 (Spec R)) ⟶ Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := ν) (Spec R) :=
  Over.homMk (quotientClassifyingMap R N) (quotientClassifyingMap_over R N)

theorem quotientClassifyingMap_on_chart (D : QuotientClassifyingCharts.Grassmannian.PrincipalQuotientChart R N) :
    D.scheme.hom ≫ quotientClassifyingMap R N = D.classifyingMap.left := by
  apply Scheme.Cover.hom_ext ((quotientPrincipalCover R N).openCover.pullback₁ D.scheme.hom)
  intro p
  change PrimeSpectrum R at p
  let E := (QuotientClassifyingCharts.Grassmannian.principalQuotientChartAt R N p).val
  change pullback.fst D.scheme.hom E.scheme.hom ≫
    (D.scheme.hom ≫ quotientClassifyingMap R N) =
      pullback.fst D.scheme.hom E.scheme.hom ≫ D.classifyingMap.left
  let T : Over (Spec R) := Over.mk (pullback.fst D.scheme.hom E.scheme.hom ≫ D.scheme.hom)
  let f : T ⟶ D.scheme := Over.homMk (pullback.fst D.scheme.hom E.scheme.hom)
  let g : T ⟶ E.scheme := Over.homMk (pullback.snd D.scheme.hom E.scheme.hom) pullback.condition.symm
  have h := congrArg Over.Hom.left (E.classifyingMaps_agree D g f)
  rw [← Category.assoc, pullback.condition, Category.assoc]
  have he : E.scheme.hom ≫ quotientClassifyingMap R N = E.classifyingMap.left :=
    quotientClassifyingMap_chart R N p
  exact (congrArg (fun k => pullback.snd D.scheme.hom E.scheme.hom ≫ k) he).trans h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientClassifyingMap.Grassmannian
