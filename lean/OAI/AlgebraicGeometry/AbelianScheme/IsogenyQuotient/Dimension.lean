import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PELAction
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Dimension.Construction

noncomputable section

/-!
Finite surjective quotients preserve the fixed relative dimension needed
by ReferenceFamily. The dimension is read from the actual scheme fibers and smooth
charts; it is not an extra condition on FiniteDescent's quotient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem fiber_dimension_eq_of_finite_surjective
    {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    [IsFinite f.left] [Surjective f.left] (s : S) :
    topologicalKrullDim (A.hom.fiber s) = topologicalKrullDim (B.hom.fiber s) := by
  let t := (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.geometricPoint S s).hom
  let fs := ((Over.pullback t).map f).left
  have : IsFinite fs := MorphismProperty.overPullbackMap (P := @IsFinite) t f inferInstance
  have : Surjective fs := MorphismProperty.overPullbackMap (P := @Surjective) t f inferInstance
  exact (ArithmeticGeometry.OrdinaryLocus.Openness.GeometricDimension.Construction.topologicalKrullDim_geometricFiber A s).symm.trans
    ((ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension.Construction.topologicalKrullDim_eq_of_integral_surjective fs).trans
      (ArithmeticGeometry.OrdinaryLocus.Openness.GeometricDimension.Construction.topologicalKrullDim_geometricFiber B s))

/-- For a smooth proper connected group scheme, a constant value of the
actual fiber dimension supplies the fixed-dimension smooth charts. -/
theorem smooth_dimension_of_fiber_dimensions
    {S : Scheme.{u}} (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (g : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim (A.toOver.hom.fiber s) = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g A.toOver.hom := by
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth A.toOver.hom x
  let : Algebra Γ(S, U) Γ(A.toOver.left, V) := (A.toOver.hom.appLE U V e).hom.toAlgebra
  change Algebra.IsStandardSmooth Γ(S, U) Γ(A.toOver.left, V) at hstd
  obtain ⟨idx, rel, hrel, hidx, ⟨P⟩⟩ := hstd
  let := hrel
  let := hidx
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  have hchart := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothDimensionCharts.Construction.smoothOfRelativeDimension_resLE_of_appLE
    A.toOver.hom P.dimension U V hU hV e hP
  let B : Over S := Over.mk (V.ι ≫ A.toOver.hom)
  let i : B ⟶ A.toOver := Over.homMk V.ι
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : SmoothOfRelativeDimension P.dimension B.hom := by
    change SmoothOfRelativeDimension P.dimension (V.ι ≫ A.toOver.hom)
    rw [← Scheme.Hom.resLE_comp_ι A.toOver.hom e]
    have : SmoothOfRelativeDimension P.dimension (A.toOver.hom.resLE U V e) := hchart
    exact inferInstanceAs
      (SmoothOfRelativeDimension (P.dimension + 0) (A.toOver.hom.resLE U V e ≫ U.ι))
  have hd := ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A.toOver B i P.dimension
    (A.toOver.hom x) ⟨⟨x, hx⟩, rfl⟩
  have heq : P.dimension = g := by exact_mod_cast hd.symm.trans (hdim (A.toOver.hom x))
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  exact heq ▸ hP

/-- The fixed relative dimension of an abelian scheme passes through a
finite surjective quotient, using FiniteDescent's already-proved smoothness. -/
theorem quotient_smooth_dimension
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (f : A.scheme ⟶ B.toOver)
    [IsFinite f.left] [Surjective f.left] : SmoothOfRelativeDimension g B.toOver.hom := by
  apply smooth_dimension_of_fiber_dimensions B g
  intro s
  have hs : s ∈ Set.range A.scheme.hom := by
    refine ⟨η[A.scheme].left s, ?_⟩
    change (η[A.scheme].left ≫ A.scheme.hom) s = s
    simp
  have : IsOpenImmersion (𝟙 A.scheme : A.scheme ⟶ A.scheme).left :=
    inferInstanceAs (IsOpenImmersion (𝟙 A.scheme.left))
  exact (fiber_dimension_eq_of_finite_surjective f s).symm.trans
    (ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A.scheme A.scheme (𝟙 _) g s hs)

/-- FiniteDescent's quotient upgraded to ReferenceFamily's actual fixed-dimension abelian
scheme. All scheme and group operations are the original quotient's. -/
def abelianQuotientWithDimension
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (f : A.scheme ⟶ B.toOver)
    [IsFinite f.left] [Surjective f.left] : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S where
  scheme := B.toOver
  group := B.group
  commutative := B.commutative
  proper := B.proper
  smoothDimension := quotient_smooth_dimension A B f
  connected := B.geometricallyConnected

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Dimension.Construction
