import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Hom
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication

/-! # Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Finite.Construction

noncomputable section

/-! A finite morphism between abelian schemes of the same relative
dimension is surjective over the full base. A group morphism is flat. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem abelian_geometric_topologicalKrullDim {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) :
    topologicalKrullDim A.scheme.left = (g : WithBot ℕ∞) := by
  have : JacobsonSpace A.scheme.left := LocallyOfFiniteType.jacobsonSpace A.scheme.hom
  have : Nonempty A.scheme.left := ⟨(1 : 𝟙_ (Over (Spec (.of k))) ⟶ A.scheme).left (IsLocalRing.closedPoint k)⟩
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := A.scheme.left) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have he := ArithmeticGeometry.OrdinaryLocus.Openness.GroupDimension.Construction.topologicalKrullDim_eq_stalk_of_transitive_closedPoints A.scheme.left
    (fun x y hx hy => by
      obtain ⟨e, _, hxy, _⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.FlatTranslations.Construction.multiplication_transitive_automorphisms A.scheme 1 x y hx hy
      exact ⟨e, hxy⟩) x hx
  exact he.trans (ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension g A.scheme.hom x hx)

theorem finite_geometric_abelian_hom_surjective {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (f : A.scheme ⟶ B.scheme) [IsFinite f.left] : Surjective f.left := by
  have : IsIntegral A.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A.scheme
  have : IsIntegral B.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group B.scheme
  apply Finite.EqualDimensionSurjectivity.Construction.finite_same_dimension_surjective f.left
  · exact (abelian_geometric_topologicalKrullDim A).trans (abelian_geometric_topologicalKrullDim B).symm
  · rw [abelian_geometric_topologicalKrullDim]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top g)

variable {S : Scheme.{u}} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (f : A.scheme ⟶ B.scheme) [IsFinite f.left]

set_option backward.isDefEq.respectTransparency false in
theorem relativeFiniteAbelianHom_surjective : Surjective f.left := by
  apply Multiplication.Construction.surjective_of_geometric_baseChanges f
  intro K _ _ s
  have : IsFinite ((Over.pullback s).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) s f inferInstance
  exact finite_geometric_abelian_hom_surjective (A.pullback s) (B.pullback s) ((Over.pullback s).map f)

theorem relativeFiniteAbelianHom_flat [IsMonHom f] : Flat f.left := by
  have : Surjective f.left := relativeFiniteAbelianHom_surjective A B f
  exact Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat f

def relativeFiniteAbelianHomIsogeny [IsMonHom f] : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B where
  hom := f
  preservesGroup := inferInstance
  finite := inferInstance
  flat := relativeFiniteAbelianHom_flat A B f
  surjective := relativeFiniteAbelianHom_surjective A B f

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Finite.Construction
