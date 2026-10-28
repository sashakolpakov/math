import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.AtlasMaps

/-! # Chart Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.ChartBaseChange.Grassmannian

noncomputable section

/-!
Normalized quotient charts commute with arbitrary changes of base scheme.
The Cartesian square is proved directly from their matrix-valued points.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [DecidableEq ι]
variable (a : ι → ν) (S : Scheme.{u})

def chartHomMatrix {X : Scheme.{u}} (g : X ⟶ (Chart.Grassmannian.normalizedChart a S).left) :
    Matrix ι ν Γ(X, ⊤) :=
  (Chart.Grassmannian.universalNormalizedMatrix a S).map g.appTop.hom

theorem chartHomMatrix_normalized {X : Scheme.{u}} (g : X ⟶ (Chart.Grassmannian.normalizedChart a S).left) :
    Matrices.Grassmannian.IsNormalized a (chartHomMatrix a S g) :=
  (Chart.Grassmannian.universalNormalizedMatrix_normalized a S).map g.appTop.hom

theorem chartHomMatrix_comp {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ (Chart.Grassmannian.normalizedChart a S).left) :
    chartHomMatrix a S (g ≫ h) = (chartHomMatrix a S h).map g.appTop.hom := rfl

theorem chartHomMatrix_id : chartHomMatrix a S (𝟙 _) = Chart.Grassmannian.universalNormalizedMatrix a S := rfl

theorem chartHom_ext {X : Scheme.{u}} {g h : X ⟶ (Chart.Grassmannian.normalizedChart a S).left}
    (hb : g ≫ (Chart.Grassmannian.normalizedChart a S).hom = h ≫ (Chart.Grassmannian.normalizedChart a S).hom)
    (hQ : chartHomMatrix a S g = chartHomMatrix a S h) : g = h := by
  let T : Over S := Over.mk (g ≫ (Chart.Grassmannian.normalizedChart a S).hom)
  let g' : T ⟶ Chart.Grassmannian.normalizedChart a S := Over.homMk g
  let h' : T ⟶ Chart.Grassmannian.normalizedChart a S := Over.homMk h hb.symm
  have he : g' = h' := by
    apply AtlasMaps.Grassmannian.chartMatrix_injective a S T
    change ((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app (.op T) g').val =
      ((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app (.op T) h').val
    rw [Chart.Grassmannian.normalizedChartRepresentation_apply, Chart.Grassmannian.normalizedChartRepresentation_apply]
    exact hQ
  exact congrArg Over.Hom.left he

def chartHomOfMatrix {X : Scheme.{u}} (f : X ⟶ S)
    (Q : Matrix ι ν Γ(X, ⊤)) (hQ : Matrices.Grassmannian.IsNormalized a Q) : X ⟶ (Chart.Grassmannian.normalizedChart a S).left :=
  (((Chart.Grassmannian.normalizedChartRepresentation a S).app (.op (Over.mk f))).inv ⟨Q, hQ⟩).left

theorem chartHomOfMatrix_over {X : Scheme.{u}} (f : X ⟶ S)
    (Q : Matrix ι ν Γ(X, ⊤)) (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    chartHomOfMatrix a S f Q hQ ≫ (Chart.Grassmannian.normalizedChart a S).hom = f :=
  (((Chart.Grassmannian.normalizedChartRepresentation a S).app (.op (Over.mk f))).inv ⟨Q, hQ⟩).w

theorem chartHomOfMatrix_matrix {X : Scheme.{u}} (f : X ⟶ S)
    (Q : Matrix ι ν Γ(X, ⊤)) (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    chartHomMatrix a S (chartHomOfMatrix a S f Q hQ) = Q := by
  have h := congrArg Subtype.val
    (((Chart.Grassmannian.normalizedChartRepresentation a S).app (.op (Over.mk f))).toEquiv.apply_symm_apply
      ⟨Q, hQ⟩)
  change ((Chart.Grassmannian.normalizedChartRepresentation a S).hom.app (.op (Over.mk f))
    (((Chart.Grassmannian.normalizedChartRepresentation a S).app (.op (Over.mk f))).inv ⟨Q, hQ⟩)).val = Q at h
  rw [Chart.Grassmannian.normalizedChartRepresentation_apply] at h
  exact h

variable {S} {T : Scheme.{u}} (f : T ⟶ S)

def normalizedChartBaseMap : (Chart.Grassmannian.normalizedChart a T).left ⟶ (Chart.Grassmannian.normalizedChart a S).left :=
  chartHomOfMatrix a S ((Chart.Grassmannian.normalizedChart a T).hom ≫ f)
    (Chart.Grassmannian.universalNormalizedMatrix a T) (Chart.Grassmannian.universalNormalizedMatrix_normalized a T)

theorem normalizedChartBaseMap_over :
    normalizedChartBaseMap a f ≫ (Chart.Grassmannian.normalizedChart a S).hom = (Chart.Grassmannian.normalizedChart a T).hom ≫ f :=
  chartHomOfMatrix_over a S _ _ _

theorem normalizedChartBaseMap_matrix :
    chartHomMatrix a S (normalizedChartBaseMap a f) = Chart.Grassmannian.universalNormalizedMatrix a T :=
  chartHomOfMatrix_matrix a S _ _ _

theorem normalizedChartBaseMap_isPullback :
    IsPullback (normalizedChartBaseMap a f) (Chart.Grassmannian.normalizedChart a T).hom (Chart.Grassmannian.normalizedChart a S).hom f where
  w := normalizedChartBaseMap_over a f
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s => by
    let Q := chartHomMatrix a S s.fst
    let hQ : Matrices.Grassmannian.IsNormalized a Q := chartHomMatrix_normalized a S s.fst
    let l := chartHomOfMatrix a T s.snd Q hQ
    have hl : l ≫ (Chart.Grassmannian.normalizedChart a T).hom = s.snd := chartHomOfMatrix_over a T _ _ _
    have hlQ : chartHomMatrix a T l = Q := chartHomOfMatrix_matrix a T _ _ _
    refine ⟨l, ?_, hl, ?_⟩
    · change l ≫ normalizedChartBaseMap a f = s.fst
      apply chartHom_ext a S
      · rw [Category.assoc, normalizedChartBaseMap_over, ← Category.assoc, hl]
        exact s.condition.symm
      · rw [chartHomMatrix_comp, normalizedChartBaseMap_matrix]
        exact hlQ
    · intro m hm hn
      change s.pt ⟶ (Chart.Grassmannian.normalizedChart a T).left at m
      change m ≫ normalizedChartBaseMap a f = s.fst at hm
      change m ≫ (Chart.Grassmannian.normalizedChart a T).hom = s.snd at hn
      change m = l
      apply chartHom_ext a T
      · exact hn.trans hl.symm
      · have h := congrArg (chartHomMatrix a S) hm
        rw [chartHomMatrix_comp, normalizedChartBaseMap_matrix] at h
        exact h.trans hlQ.symm)⟩

theorem normalizedChartBaseMap_id : normalizedChartBaseMap a (𝟙 S) = 𝟙 _ := by
  apply chartHom_ext a S
  · rw [normalizedChartBaseMap_over, Category.comp_id, Category.id_comp]
  · rw [normalizedChartBaseMap_matrix, chartHomMatrix_id]

theorem normalizedChartBaseMap_comp {U : Scheme.{u}} (g : U ⟶ T) :
    normalizedChartBaseMap a (g ≫ f) = normalizedChartBaseMap a g ≫ normalizedChartBaseMap a f := by
  apply chartHom_ext a S
  · rw [normalizedChartBaseMap_over, Category.assoc, normalizedChartBaseMap_over,
      ← Category.assoc (normalizedChartBaseMap a g), normalizedChartBaseMap_over, Category.assoc]
  · rw [normalizedChartBaseMap_matrix, chartHomMatrix_comp, normalizedChartBaseMap_matrix]
    exact (normalizedChartBaseMap_matrix a g).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.ChartBaseChange.Grassmannian
