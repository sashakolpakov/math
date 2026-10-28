import OAI.RepresentationTheory.Theta.Geometric.ConstantSchemeDegree
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Affine Product Rank -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineProductRank

noncomputable section

/-! The rank of an actual affine product over a field is computed
through its native tensor-product coordinate algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

variable (k : Type) [Field k]

abbrev affine (A : Type) [CommRing A] [Algebra k A] :=
  (algSpec (.of k)).obj (.op (CommAlgCat.of k A))

theorem affine_finite (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] :
    IsFinite (affine k A).hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem affine_flat (A : Type) [CommRing A] [Algebra k A] :
    Flat (affine k A).hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem affine_rank (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A]
    (z : Spec (.of k)) : (affine k A).hom.finrank z = Module.finrank k A :=
  (Scheme.Hom.finrank_SpecMap_algebraMap k A z).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := A)) z)

theorem affine_product_rank (A B : Type) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Finite k A] [Module.Finite k B]
    (z : Spec (.of k)) :
    (affine k A ⊗ affine k B).hom.finrank z = Module.finrank k A * Module.finrank k B := by
  let F := algSpec (CommRingCat.of k)
  let : F.Braided := braidedAlgSpec
  let e := Functor.Monoidal.μIso F (.op (CommAlgCat.of k A)) (.op (CommAlgCat.of k B))
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : IsFinite (affine k (A ⊗[k] B)).hom := affine_finite k _
  have : Flat (affine k (A ⊗[k] B)).hom := affine_flat k _
  calc
    (affine k A ⊗ affine k B).hom.finrank z = (affine k (A ⊗[k] B)).hom.finrank z := by
      rw [← e.hom.w]
      exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom.left _) z
    _ = Module.finrank k (A ⊗[k] B) := affine_rank k _ z
    _ = Module.finrank k A * Module.finrank k B := Module.finrank_tensorProduct

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineProductRank
