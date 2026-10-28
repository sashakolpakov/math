import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentAffineCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ParameterOverlapIdeals
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.SubschemeDescent

/-! # Parameter Affine Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ParameterAffineGluing

noncomputable section

/-! Closed representations on affine parameter charts glue when the
parameter condition is local on the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S) (F : Subfunctor (yoneda.obj B))

theorem closed_parameter_of_affine_charts
    (hlocal : ∀ (T : Over S) (D : T.left.OpenCover.{u}) (x : T ⟶ B),
      (∀ i, (Over.homMk (D.f i) rfl : Over.mk (D.f i ≫ T.hom) ⟶ T) ≫ x ∈
        F.obj (.op (Over.mk (D.f i ≫ T.hom)))) → x ∈ F.obj (.op T))
    (hcharts : ∀ i : B.left.affineOpenCover.I₀,
      ∃ (Z : Over S) (j : Z ⟶ Intrinsic.ContainmentAffineCharts.affineParameterChart B i), IsClosedImmersion j.left ∧
        ∀ (T : Over S) (x : T ⟶ Intrinsic.ContainmentAffineCharts.affineParameterChart B i),
          x ≫ Intrinsic.ContainmentAffineCharts.affineParameterChartInclusion B i ∈ F.obj (.op T) ↔
            ∃! y : T ⟶ Z, y ≫ j = x) :
    ∃ (Z : Over S) (j : Z ⟶ B), IsClosedImmersion j.left ∧
      ∀ (T : Over S) (x : T ⟶ B), x ∈ F.obj (.op T) ↔ ∃! y : T ⟶ Z, y ≫ j = x := by
  classical
  choose Z c hc ht using hcharts
  let C := B.left.affineOpenCover
  let : ∀ i, IsClosedImmersion (c i).left := hc
  have hcompat (i j : C.I₀) :
      (c i).left.ker.comap (pullback.fst (C.f i) (C.f j)) =
        (c j).left.ker.comap (pullback.snd (C.f i) (C.f j)) := by
    let W : Over S := Over.mk (pullback.fst (C.f i) (C.f j) ≫ C.f i ≫ B.hom)
    let p : W ⟶ Intrinsic.ContainmentAffineCharts.affineParameterChart B i := Over.homMk (pullback.fst (C.f i) (C.f j)) rfl
    let q : W ⟶ Intrinsic.ContainmentAffineCharts.affineParameterChart B j := Over.homMk (pullback.snd (C.f i) (C.f j))
      (pullback.condition_assoc B.hom).symm
    exact ParameterOverlapIdeals.closedParameter_overlap_ideals F (Intrinsic.ContainmentAffineCharts.affineParameterChartInclusion B i)
      (Intrinsic.ContainmentAffineCharts.affineParameterChartInclusion B j) (c i) (c j) (ht i) (ht j) p q
      (Over.OverMorphism.ext pullback.condition)
  obtain ⟨J, hJ⟩ := @SubschemeDescent.closed_subscheme_descent B.left C.openCover (fun i => (Z i).left)
    (fun i => (c i).left) (fun i => hc i) hcompat
  let W : Over S := Over.mk (J.subschemeι ≫ B.hom)
  let j : W ⟶ B := Over.homMk J.subschemeι rfl
  let : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion J.subschemeι)
  refine ⟨W, j, inferInstanceAs (IsClosedImmersion J.subschemeι), ?_⟩
  intro T x
  let D : T.left.OpenCover.{u} := C.openCover.pullback₁ x.left
  have htest (i : C.I₀) :
      (Over.homMk (D.f i) rfl : Over.mk (D.f i ≫ T.hom) ⟶ T) ≫ x ∈
        F.obj (.op (Over.mk (D.f i ≫ T.hom))) ↔
          (J.comap x.left).comap (D.f i) = ⊥ := by
    let V : Over S := Over.mk (D.f i ≫ T.hom)
    let t : V ⟶ T := Over.homMk (D.f i) rfl
    let z₀ := C.openCover.pullbackHom x.left i
    have hz₀ : z₀ ≫ C.f i = D.f i ≫ x.left := C.openCover.pullbackHom_map x.left i
    have hw : z₀ ≫ (Intrinsic.ContainmentAffineCharts.affineParameterChart B i).hom = V.hom :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ B.hom) hz₀).trans
          ((Category.assoc _ _ _).trans (congrArg (fun k => D.f i ≫ k) x.w)))
    let z : V ⟶ Intrinsic.ContainmentAffineCharts.affineParameterChart B i := Over.homMk z₀ hw
    have hz : z ≫ Intrinsic.ContainmentAffineCharts.affineParameterChartInclusion B i = t ≫ x := Over.OverMorphism.ext hz₀
    have he : (J.comap x.left).comap (D.f i) = (c i).left.ker.comap z.left := by
      calc
        _ = J.comap (D.f i ≫ x.left) := (J.comap_comp _ _).symm
        _ = J.comap (z₀ ≫ C.f i) := congrArg (fun k => J.comap k) hz₀.symm
        _ = (J.comap (C.f i)).comap z₀ := J.comap_comp _ _
        _ = _ := congrArg (fun L => L.comap z₀) (hJ i)
    have h := ht i V z
    rw [hz, FactorizationCriterion.over_closed_factorization_iff_comap_bot, ← he] at h
    exact h
  have hzero : x ∈ F.obj (.op T) ↔ J.comap x.left = ⊥ := by
    constructor
    · intro hx
      apply AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality.ideal_eq_of_open_cover D
      intro i
      rw [Scheme.IdealSheafData.comap_bot]
      exact (htest i).mp (F.map (Over.homMk (D.f i) rfl :
        Over.mk (D.f i ≫ T.hom) ⟶ T).op hx)
    · intro hx
      apply hlocal T D x
      intro i
      apply (htest i).mpr
      rw [hx, Scheme.IdealSheafData.comap_bot]
  have hj : j.left.ker = J := J.ker_subschemeι
  exact hzero.trans (by rw [← hj]; exact (FactorizationCriterion.over_closed_factorization_iff_comap_bot j x).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ParameterAffineGluing
