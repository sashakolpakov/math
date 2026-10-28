import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Abelian Dimension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianDimension.CM

noncomputable section

/-! The smooth proper connected groups furnished by IntegralModel have a fixed
relative dimension over a connected arithmetic base. This proves the
dimension field required by the actual abelian-scheme interface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction

variable {S : Scheme} [PreconnectedSpace S] (A : Over S)
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom]
  [GeometricallyConnected A.hom]

theorem fixed_relative_dimension (s : S) :
    SmoothOfRelativeDimension (ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction.fiberDimension A s) A.hom := by
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth A.hom x
  let : Algebra Γ(S, U) Γ(A.left, V) := (A.hom.appLE U V e).hom.toAlgebra
  change Algebra.IsStandardSmooth Γ(S, U) Γ(A.left, V) at hstd
  obtain ⟨I, J, hJ, hI, ⟨P⟩⟩ := hstd
  let := hJ
  let := hI
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  let B : Over S := Over.mk (V.ι ≫ A.hom)
  let i : B ⟶ A := Over.homMk V.ι
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : SmoothOfRelativeDimension P.dimension (A.hom.resLE U V e) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.SmoothDimensionCharts.Construction.smoothOfRelativeDimension_resLE_of_appLE A.hom P.dimension U V hU hV e hP
  have : SmoothOfRelativeDimension P.dimension B.hom := by
    change SmoothOfRelativeDimension P.dimension (V.ι ≫ A.hom)
    rw [← Scheme.Hom.resLE_comp_ι A.hom e]
    exact inferInstanceAs
      (SmoothOfRelativeDimension (P.dimension + 0) (A.hom.resLE U V e ≫ U.ι))
  have hdim := ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction.dimension_fiber_of_smooth_chart A B i P.dimension (A.hom x)
    ⟨⟨x, hx⟩, rfl⟩
  rw [ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction.fiberDimension_spec] at hdim
  have hc := (ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction.isLocallyConstant_fiberDimension A).apply_eq_of_preconnectedSpace
    (A.hom x) s
  have hn : ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction.fiberDimension A s = P.dimension := by
    rw [hc] at hdim
    exact_mod_cast hdim
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  rw [hn]
  exact hP

/-- Package the same group scheme as an HilbertConstruction abelian scheme. Its group,
structure morphism, and underlying scheme are unchanged by this construction. -/
def abelianScheme (s : S) : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimension.Construction.fiberDimension A s) S where
  scheme := A
  group := inferInstance
  commutative := inferInstance
  proper := inferInstance
  smoothDimension := fixed_relative_dimension A s
  connected := inferInstance

theorem abelianScheme_scheme (s : S) : (abelianScheme A s).scheme = A := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AbelianDimension.CM
