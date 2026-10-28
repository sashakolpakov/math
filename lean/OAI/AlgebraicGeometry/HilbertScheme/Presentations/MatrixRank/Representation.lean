import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Monomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization

/-! # Representation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Representation.Grassmannian

noncomputable section

/-! The glued matrix-rank scheme represents the condition of locally factoring
through the explicit determinant-and-residual pivot loci, on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

def matrixRankLocalCondition {T : Over S} (x : T ⟶ M) : Prop :=
  ∃ U : T.left.OpenCover.{u}, ∀ i, ∃ p : MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν,
    ∃ g : U.X i ⟶ (MatrixPivot.Charts.Grassmannian.matrixPivotChart M A p).left,
      g ≫ (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left = U.f i ≫ x.left

theorem matrixRankLocalCondition_iff_lift {T : Over S} (x : T ⟶ M) :
    matrixRankLocalCondition (ι := ι) M A x ↔
      ∃! y : T ⟶ Data.Grassmannian.matrixRankOver (ι := ι) M A, y ≫ Data.Grassmannian.matrixRankParameterMap M A = x := by
  constructor
  · rintro ⟨U, hU⟩
    obtain ⟨g, hg, _⟩ := Local.MorphismFactorization.lift_of_openCover U x.left (Data.Grassmannian.matrixRankStructureMap (ι := ι) M A) (by
      intro i
      obtain ⟨p, k, hk⟩ := hU i
      refine ⟨k ≫ Data.Grassmannian.matrixRankChartMap M A p, ?_⟩
      rw [Category.assoc, Data.Grassmannian.matrixRankChartMap_structureMap]
      exact hk)
    let y : T ⟶ Data.Grassmannian.matrixRankOver (ι := ι) M A := Over.homMk g (by
      change g ≫ (Data.Grassmannian.matrixRankStructureMap M A ≫ M.hom) = T.hom
      rw [← Category.assoc, hg, x.w])
    have hy : y ≫ Data.Grassmannian.matrixRankParameterMap M A = x := Over.OverMorphism.ext hg
    exact ⟨y, hy, fun z hz => (cancel_mono (Data.Grassmannian.matrixRankParameterMap M A)).mp (hz.trans hy.symm)⟩
  · rintro ⟨y, hy, _⟩
    let G := Data.Grassmannian.matrixRankGlueData (ι := ι) M A
    let yl : T.left ⟶ G.glued := y.left
    let s : G.glued ⟶ M.left := Data.Grassmannian.matrixRankStructureMap M A
    let U := G.openCover.pullback₁ yl
    refine ⟨U, ?_⟩
    intro p
    change MatrixPivot.Charts.Grassmannian.MatrixPivotIndex ι μ ν at p
    refine ⟨p, G.openCover.pullbackHom yl p, ?_⟩
    have hc : G.openCover.f p ≫ s = (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left :=
      Data.Grassmannian.matrixRankChartMap_structureMap M A p
    have hys : yl ≫ s = x.left := congrArg Over.Hom.left hy
    calc
      G.openCover.pullbackHom yl p ≫ (MatrixPivot.Charts.Grassmannian.matrixPivotChartInclusion M A p).left =
          G.openCover.pullbackHom yl p ≫ (G.openCover.f p ≫ s) := congrArg _ hc.symm
      _ = (U.f p ≫ yl) ≫ s := (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ s) (G.openCover.pullbackHom_map yl p))
      _ = U.f p ≫ x.left := (Category.assoc _ _ _).trans (congrArg _ hys)

def matrixRankSubfunctor : Subfunctor (yoneda.obj M) where
  obj _T := {x | matrixRankLocalCondition (ι := ι) M A x}
  map a x hx := by
    obtain ⟨y, hy, _⟩ := (matrixRankLocalCondition_iff_lift M A x).mp hx
    apply (matrixRankLocalCondition_iff_lift M A (a.unop ≫ x)).mpr
    have h : (a.unop ≫ y) ≫ Data.Grassmannian.matrixRankParameterMap M A = a.unop ≫ x := by
      rw [Category.assoc, hy]
    exact ⟨a.unop ≫ y, h,
      fun z hz => (cancel_mono (Data.Grassmannian.matrixRankParameterMap M A)).mp (hz.trans h.symm)⟩

def matrixRankPointMap : yoneda.obj (Data.Grassmannian.matrixRankOver (ι := ι) M A) ⟶
    (matrixRankSubfunctor (ι := ι) M A).toFunctor where
  app _T := ↾fun y => ⟨y ≫ Data.Grassmannian.matrixRankParameterMap M A,
    (matrixRankLocalCondition_iff_lift M A _).mpr
      ⟨y, rfl, fun z hz => (cancel_mono (Data.Grassmannian.matrixRankParameterMap M A)).mp hz⟩⟩
  naturality _ _ a := by
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    exact Category.assoc _ _ _

instance matrixRankPointMap_isIso : IsIso (matrixRankPointMap (ι := ι) M A) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro T
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    exact (cancel_mono (Data.Grassmannian.matrixRankParameterMap M A)).mp (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy, _⟩ := (matrixRankLocalCondition_iff_lift M A x.val).mp x.property
    exact ⟨y, Subtype.ext hy⟩

def matrixRankRepresentation : yoneda.obj (Data.Grassmannian.matrixRankOver (ι := ι) M A) ≅
    (matrixRankSubfunctor (ι := ι) M A).toFunctor := asIso (matrixRankPointMap M A)

theorem matrixRankRepresentation_inclusion :
    (matrixRankRepresentation (ι := ι) M A).hom ≫ (matrixRankSubfunctor (ι := ι) M A).ι =
      yoneda.map (Data.Grassmannian.matrixRankParameterMap (ι := ι) M A) := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixRank.Representation.Grassmannian
