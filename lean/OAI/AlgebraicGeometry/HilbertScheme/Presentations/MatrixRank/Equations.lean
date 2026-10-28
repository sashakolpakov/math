import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Representation

/-! # Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Equations.Grassmannian

noncomputable section

/-! The represented local rank condition is exactly local invertibility of a
pivot determinant together with vanishing of its explicit polynomial residual. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

theorem matrixPivotChart_factorization_iff (p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν)
    {T : Scheme.{u}} (x : T ⟶ M.left) :
    MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id)
      (A.submatrix id p.1) A x.appTop.hom ↔
      ∃! g : T ⟶ (MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p).left,
        g ≫ (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left = x := by
  let XT : Over S := Over.mk (x ≫ M.hom)
  let f : XT ⟶ M := Over.homMk x rfl
  constructor
  · intro hx
    let g := MatrixPivot.Charts.Grassmannian.matrixPivotChartLift M A p f hx
    have hg : g.left ≫ (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left = x :=
      congrArg Over.Hom.left (MatrixPivot.Charts.Grassmannian.matrixPivotChartLift_inclusion M A p f hx)
    exact ⟨g.left, hg,
      fun k hk => (cancel_mono (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left).mp (hk.trans hg.symm)⟩
  · rintro ⟨g, hg, _⟩
    let k : XT ⟶ MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p := Over.homMk g (by
      rw [← (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).w, ← Category.assoc, hg]
      rfl)
    have hk : k ≫ MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p = f := Over.OverMorphism.ext hg
    have h := MatrixPivot.Charts.Grassmannian.matrixPivotChart_condition M A p k
    rw [hk] at h
    exact h

theorem matrixRankLocalCondition_iff_equations {T : Over S} (x : T ⟶ M) :
    Representation.Grassmannian.matrixRankLocalCondition (ι := ι) M A x ↔
      ∃ U : T.left.OpenCover.{u}, ∀ i, ∃ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν,
        MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id)
          (A.submatrix id p.1) A (U.f i ≫ x.left).appTop.hom := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i => ?_⟩
    obtain ⟨p, g, hg⟩ := hU i
    refine ⟨p, (matrixPivotChart_factorization_iff M A p _).mpr ?_⟩
    exact ⟨g, hg,
      fun k hk => (cancel_mono (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left).mp (hk.trans hg.symm)⟩
  · rintro ⟨U, hU⟩
    refine ⟨U, fun i => ?_⟩
    obtain ⟨p, hp⟩ := hU i
    obtain ⟨g, hg, _⟩ := (matrixPivotChart_factorization_iff M A p _).mp hp
    exact ⟨p, g, hg⟩

theorem matrixRankRepresentation_equations {T : Over S} (x : T ⟶ M) :
    (∃ U : T.left.OpenCover.{u}, ∀ i, ∃ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν,
      MatrixPivot.Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id)
        (A.submatrix id p.1) A (U.f i ≫ x.left).appTop.hom) ↔
      ∃! y : T ⟶ Data.Grassmannian.matrixRankOver (ι := ι) M A, y ≫ Data.Grassmannian.matrixRankParameterMap M A = x :=
  (matrixRankLocalCondition_iff_equations M A x).symm.trans (Representation.Grassmannian.matrixRankLocalCondition_iff_lift M A x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Equations.Grassmannian
