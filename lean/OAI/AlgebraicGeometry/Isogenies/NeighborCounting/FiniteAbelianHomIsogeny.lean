import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.Hom
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Fiberwise

/-! # Finite Abelian Hom Isogeny -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteAbelianHomIsogeny

noncomputable section

/-! A finite homomorphism of abelian schemes with the same relative
dimension is an isogeny. The geometric-fiber criterion supplies
surjectivity over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (f : A.scheme ⟶ B.scheme) [IsFinite f.left]

theorem finite_abelian_hom_surjective_over_base : Surjective f.left := by
  apply AbelianScheme.IsogenyQuotient.Multiplication.Construction.surjective_of_geometric_baseChanges f
  intro k _ _ t
  let f' : (A.pullback t).scheme ⟶ (B.pullback t).scheme := (Over.pullback t).map f
  have : IsFinite f'.left := MorphismProperty.overPullbackMap (P := @IsFinite) t f inferInstance
  exact AbelianScheme.IsogenyQuotient.Finite.Hom.Construction.finite_abelian_hom_surjective (A.pullback t) (B.pullback t) f'

def finiteAbelianHomIsogenyOverBase [IsMonHom f] : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B := by
  have : Surjective f.left := finite_abelian_hom_surjective_over_base A B f
  exact {
    hom := f
    preservesGroup := inferInstance
    finite := inferInstance
    flat := AbelianScheme.IsogenyQuotient.Finite.GroupHomFlat.Construction.finite_surjective_groupHom_flat f
    surjective := inferInstance }

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteAbelianHomIsogeny
