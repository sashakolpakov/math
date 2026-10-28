import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.TestFactorization

/-! # Containment Global Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobalFactorization.GradedHilbert

noncomputable section

/-! The glued closed native containment scheme has the exact
factorization property on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S) [IsLocallyNoetherian B.left] (n : ℕ)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B)
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B).IdealSheafData)

theorem nativeContainmentGlobalInclusion_mem :
    ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K ∈
      (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).obj
        (.op (ContainmentGlobal.GradedHilbert.nativeContainmentGlobalScheme B n F K)) := by
  let : ∀ i, IsOpenImmersion (ContainmentGlobal.GradedHilbert.nativeContainmentChartToGlobal B n F K i).left :=
    fun i => ContainmentGlobal.GradedHilbert.nativeContainmentChartToGlobal_isOpenImmersion B n F K i
  apply Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameter_of_openCover (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val
    (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart B n F K) (ContainmentGlobal.GradedHilbert.nativeContainmentChartToGlobal B n F K)
    (fun t => (ContainmentGlobal.GradedHilbert.nativeContainmentGlueData B n F K).openCover.exists_eq t)
  intro i
  rw [ContainmentGlobal.GradedHilbert.nativeContainmentChartToGlobal_inclusion]
  let j := ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i
  let : Mono j := Over.mono_of_mono_left j
  exact (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart_all_tests B n F K i (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart B n F K i) j).mpr
    ⟨𝟙 _, Category.id_comp j, fun y hy => (cancel_mono j).mp (hy.trans (Category.id_comp j).symm)⟩

theorem nativeContainmentGlobal_lift (T : Over S) (x : T ⟶ B)
    (hx : x ∈ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).obj (.op T)) :
    ∃! y : T ⟶ ContainmentGlobal.GradedHilbert.nativeContainmentGlobalScheme B n F K,
      y ≫ ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K = x := by
  let C := B.left.affineOpenCover.openCover
  let D := C.pullback₁ x.left
  let L := Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val
  apply Affine.TestFactorization.over_lift_of_openCover D x (ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K)
  intro i
  let V : Over S := Over.mk (D.f i ≫ T.hom)
  let t : V ⟶ T := Over.homMk (D.f i) rfl
  let z₀ := C.pullbackHom x.left i
  have hz₀ : z₀ ≫ C.f i = D.f i ≫ x.left := C.pullbackHom_map x.left i
  have hw : z₀ ≫ (ContainmentAffineCharts.affineParameterChart B i).hom = V.hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ B.hom) hz₀).trans
        ((Category.assoc _ _ _).trans (congrArg (fun f => D.f i ≫ f) x.w)))
  let z : V ⟶ ContainmentAffineCharts.affineParameterChart B i := Over.homMk z₀ hw
  have hz : z ≫ ContainmentAffineCharts.affineParameterChartInclusion B i = t ≫ x := Over.OverMorphism.ext hz₀
  have hm : z ≫ ContainmentAffineCharts.affineParameterChartInclusion B i ∈ L.obj (.op V) := hz.symm ▸ L.map t.op hx
  obtain ⟨y, hy, _⟩ := (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart_all_tests B n F K i V z).mp hm
  refine ⟨y ≫ ContainmentGlobal.GradedHilbert.nativeContainmentChartToGlobal B n F K i, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => y ≫ f) (ContainmentGlobal.GradedHilbert.nativeContainmentChartToGlobal_inclusion B n F K i)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ ContainmentAffineCharts.affineParameterChartInclusion B i) hy).trans hz)))

theorem nativeContainmentGlobal_all_tests (T : Over S) (x : T ⟶ B) :
    K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x) ≤
      (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x F).val ↔
    ∃! y : T ⟶ ContainmentGlobal.GradedHilbert.nativeContainmentGlobalScheme B n F K,
      y ≫ ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K = x := by
  constructor
  · exact nativeContainmentGlobal_lift B n F K T x
  · rintro ⟨y, hy, _⟩
    have h := (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).map y.op
      (nativeContainmentGlobalInclusion_mem B n F K)
    change y ≫ ContainmentGlobal.GradedHilbert.nativeContainmentGlobalInclusion B n F K ∈
      (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val).obj (.op T) at h
    exact hy ▸ h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobalFactorization.GradedHilbert
