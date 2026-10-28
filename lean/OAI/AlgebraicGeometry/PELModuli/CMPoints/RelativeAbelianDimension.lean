import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Relative Abelian Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeAbelianDimension

noncomputable section

/-! A smooth proper connected group over a connected base has the
relative dimension read from any one algebraically closed fiber.
This constructs the abelian-scheme adapter for the spread CM models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem group_algClosed_pullback_dimension
    {k : Type} [Field k] [IsAlgClosed k] (c : Spec (.of k) ⟶ S) :
    topologicalKrullDim ((Over.pullback c).obj A).left =
      topologicalKrullDim (A.hom.fiber (c (IsLocalRing.closedPoint k))) := by
  let s := c (IsLocalRing.closedPoint k)
  let x : A.left := η[A].left s
  have hx : A.hom x = s := by
    change (η[A].left ≫ A.hom) s = s
    simp
  obtain ⟨n, U, V, _, _, hxV, e, hn⟩ :=
    IntegralModel.SmoothDimensionCharts.DimensionSupport.exists_smoothOfRelativeDimension_chart A.hom x
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let i : B ⟶ A := Over.homMk V.ι
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  let : SmoothOfRelativeDimension n B.hom := by
    change SmoothOfRelativeDimension n (V.ι ≫ A.hom)
    rw [← Scheme.Hom.resLE_comp_ι A.hom e]
    let : SmoothOfRelativeDimension n (A.hom.resLE U V e) := hn
    exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) (A.hom.resLE U V e ≫ U.ι))
  have hs : s ∈ Set.range B.hom := ⟨⟨x, hxV⟩, hx⟩
  exact (IntegralModel.Group.FamilyDimension.dimension_algClosed_baseChange_of_smooth_chart A B i n c hs).trans
    (ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A B i n s hs).symm

theorem smoothOfRelativeDimension_of_fiber_dimensions (g : ℕ)
    (hg : ∀ s : S, topologicalKrullDim (A.hom.fiber s) = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g A.hom := by
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth A.hom x
  let : Algebra Γ(S, U) Γ(A.left, V) := (A.hom.appLE U V e).hom.toAlgebra
  change Algebra.IsStandardSmooth Γ(S, U) Γ(A.left, V) at hstd
  obtain ⟨varIndex, relIndex, hσ, hι, ⟨P⟩⟩ := hstd
  let := hσ
  let := hι
  let n := P.dimension
  have hstdn := P.isStandardSmoothOfRelativeDimension rfl
  have hn := IntegralModel.SmoothDimensionCharts.DimensionSupport.smoothOfRelativeDimension_resLE_of_appLE
    A.hom n U V hU hV e hstdn
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let i : B ⟶ A := Over.homMk V.ι
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  let : SmoothOfRelativeDimension n B.hom := by
    change SmoothOfRelativeDimension n (V.ι ≫ A.hom)
    rw [← Scheme.Hom.resLE_comp_ι A.hom e]
    let : SmoothOfRelativeDimension n (A.hom.resLE U V e) := hn
    exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) (A.hom.resLE U V e ≫ U.ι))
  have hdim := ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A B i n (A.hom x)
    ⟨⟨x, hx⟩, rfl⟩
  have hng : n = g := by exact_mod_cast hdim.symm.trans (hg (A.hom x))
  exact ⟨U, hU, V, hV, hx, e, hng ▸ hstdn⟩

theorem smoothOfRelativeDimension_of_one_fiber [ConnectedSpace S]
    {k : Type} [Field k] [IsAlgClosed k] (c : Spec (.of k) ⟶ S) (g : ℕ)
    (hg : topologicalKrullDim ((Over.pullback c).obj A).left = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g A.hom := by
  apply smoothOfRelativeDimension_of_fiber_dimensions A g
  intro s
  exact (ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction.isLocallyConstant_fiberKrullDim A).apply_eq_of_preconnectedSpace
    s (c (IsLocalRing.closedPoint k)) |>.trans ((group_algClosed_pullback_dimension A c).symm.trans hg)

def abelianSchemeOfOneFiber [ConnectedSpace S]
    {k : Type} [Field k] [IsAlgClosed k] (c : Spec (.of k) ⟶ S) (g : ℕ)
    (hg : topologicalKrullDim ((Over.pullback c).obj A).left = (g : WithBot ℕ∞)) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S where
  scheme := A
  group := inferInstance
  commutative := inferInstance
  proper := inferInstance
  connected := inferInstance
  smoothDimension := smoothOfRelativeDimension_of_one_fiber A c g hg

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeAbelianDimension
