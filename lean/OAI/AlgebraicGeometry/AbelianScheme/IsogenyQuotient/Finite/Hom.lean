import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.EqualDimensionSurjectivity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothRelativeDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Hom -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Hom.Construction

noncomputable section

/-! A finite homomorphism between abelian varieties of equal dimension
is an isogeny. Surjectivity follows from dimension and flatness from
translations of the actual smooth group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}

theorem abelian_topologicalKrullDim (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) :
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

theorem finite_abelian_hom_surjective (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (f : A.scheme ⟶ B.scheme) [IsFinite f.left] : Surjective f.left := by
  have : IsIntegral A.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A.scheme
  have : IsIntegral B.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group B.scheme
  apply EqualDimensionSurjectivity.Construction.finite_same_dimension_surjective f.left
  · exact (abelian_topologicalKrullDim A).trans (abelian_topologicalKrullDim B).symm
  · rw [abelian_topologicalKrullDim]
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top g)

def finiteAbelianHomIsogeny (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] [IsFinite f.left] : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B := by
  have : Surjective f.left := finite_abelian_hom_surjective A B f
  exact { hom := f
          preservesGroup := inferInstance
          finite := inferInstance
          flat := GroupHomFlat.Construction.finite_surjective_groupHom_flat f
          surjective := inferInstance }

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Hom.Construction
