import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricQuotient
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothDimensionCharts
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension

/-! # Quotient Dimension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
A finite surjective quotient preserves the actual dimension of a smooth
proper connected group. This upgrades the constructed FiniteDescent quotient to an
HilbertConstruction abelian scheme of the original fixed dimension.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem QuotientDimension.Construction.groupDimension_of_smooth_open
    (A C : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (i : C ⟶ A) [IsOpenImmersion i.left] [Nonempty C.left]
    (n : ℕ) [SmoothOfRelativeDimension n C.hom] :
    topologicalKrullDim A.left = (n : WithBot ℕ∞) := by
  have : Smooth C.hom := SmoothOfRelativeDimension.smooth n C.hom
  have : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨c, _, hc⟩ := nonempty_inter_closedPoints
    (X := C.left) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hic : IsClosed {i.left c} := by
    change c ∈ i.left ⁻¹' closedPoints A.left
    rw [i.left.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have hdim : topologicalKrullDim A.left = ringKrullDim (C.left.presheaf.stalk c) := by
    rw [ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction.topologicalKrullDim_eq_stalk_of_transitive_closedPoints A.left (fun x y hx hy => by
      obtain ⟨α, _, hxy, _⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.FlatTranslations.Construction.multiplication_transitive_automorphisms A 1 x y hx hy
      exact ⟨α, hxy⟩) (i.left c) hic,
      ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      coheight_eq_of_isOpenImmersion i.left]
  exact hdim.trans (ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension n C.hom c hc)

/-- The fixed relative dimension is recovered from the topological
dimension of the actual smooth group, using its standard smooth charts. -/
theorem QuotientDimension.Construction.smoothOfRelativeDimension_of_groupDimension
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (g : ℕ) (hg : topologicalKrullDim A.left = (g : WithBot ℕ∞)) :
    SmoothOfRelativeDimension g A.hom := by
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth A.hom x
  let : Algebra Γ(Spec (.of k), U) Γ(A.left, V) := (A.hom.appLE U V e).hom.toAlgebra
  change Algebra.IsStandardSmooth Γ(Spec (.of k), U) Γ(A.left, V) at hstd
  obtain ⟨indices, relations, hrelations, hindices, ⟨Q⟩⟩ := hstd
  let := hrelations
  let := hindices
  have hQ := Q.isStandardSmoothOfRelativeDimension rfl
  have : SmoothOfRelativeDimension Q.dimension (A.hom.resLE U V e) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.SmoothDimensionCharts.Construction.smoothOfRelativeDimension_resLE_of_appLE A.hom Q.dimension U V hU hV e hQ
  let C : Over (Spec (.of k)) := Over.mk (V.ι ≫ A.hom)
  let i : C ⟶ A := Over.homMk V.ι
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have : Nonempty C.left := ⟨⟨x, hx⟩⟩
  have : SmoothOfRelativeDimension Q.dimension C.hom := by
    change SmoothOfRelativeDimension Q.dimension (V.ι ≫ A.hom)
    rw [← Scheme.Hom.resLE_comp_ι A.hom e]
    exact inferInstanceAs (SmoothOfRelativeDimension (Q.dimension + 0) (A.hom.resLE U V e ≫ U.ι))
  have hn : Q.dimension = g := by
    exact_mod_cast (QuotientDimension.Construction.groupDimension_of_smooth_open A C i Q.dimension).symm.trans hg
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  exact hn ▸ hQ

variable {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable {H : Grp (Over (Spec (.of k)))} {i : H.X ⟶ A.scheme} [IsMonHom i]

variable (Q : GeometricQuotient.Construction.GeometricKernelQuotient A H i)

omit [IsMonHom i] in
theorem GeometricQuotient.Construction.GeometricKernelQuotient.target_dimension : topologicalKrullDim Q.target.toOver.left = (g : WithBot ℕ∞) := by
  have : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  let j : A.scheme ⟶ A.scheme := 𝟙 A.scheme
  have : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (𝟙 A.scheme.left))
  have hA := QuotientDimension.Construction.groupDimension_of_smooth_open A.scheme A.scheme j g
  exact (ArithmeticGeometry.OrdinaryLocus.Openness.IntegralDimension.Construction.topologicalKrullDim_eq_of_integral_surjective Q.projection.left).symm.trans hA

/-- The quotient now has HilbertConstruction's original fixed relative dimension, proved
from finiteness and surjectivity of its constructed projection. -/
def GeometricQuotient.Construction.GeometricKernelQuotient.abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)) where
  scheme := Q.target.toOver
  group := Q.target.group
  commutative := Q.target.commutative
  proper := Q.target.proper
  smoothDimension := QuotientDimension.Construction.smoothOfRelativeDimension_of_groupDimension Q.target.toOver g Q.target_dimension
  connected := Q.target.connected

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
