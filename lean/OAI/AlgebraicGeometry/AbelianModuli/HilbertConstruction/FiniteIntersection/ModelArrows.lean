import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.IntersectionModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverFunctoriality

/-! # Model Arrows -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! Faithful recovery forces the descended intersection arrows to satisfy all inclusion relations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)

def IntersectionModel.FiniteIntersectionModel.inclusionAlgebraMap {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    M.algebra S →ₐ[M.coefficients] M.algebra T := M.arrow ⟨(S, T), h⟩

theorem IntersectionModel.FiniteIntersectionModel.realization_inclusion {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val)
    (x : M.algebra S) :
    M.realization T (M.inclusionAlgebraMap h x) =
      Affine.OverMorphisms.affineOverMap R (Arrows.finiteIntersectionArrow X h) (M.realization S x) :=
  M.realization_arrow ⟨(S, T), h⟩ x

theorem IntersectionModel.FiniteIntersectionModel.inclusionAlgebraMap_id (S : Finite.AffineIntersections.finiteIntersectionIndex X) :
    M.inclusionAlgebraMap (Finset.Subset.refl S.val) = AlgHom.id M.coefficients (M.algebra S) := by
  ext x
  apply M.realization_injective S
  rw [M.realization_inclusion, Arrows.finiteIntersectionArrow_id, Affine.OverFunctoriality.affineOverMap_id]
  rfl

theorem IntersectionModel.FiniteIntersectionModel.inclusionAlgebraMap_comp {S T U : Finite.AffineIntersections.finiteIntersectionIndex X}
    (hST : S.val ⊆ T.val) (hTU : T.val ⊆ U.val) :
    (M.inclusionAlgebraMap hTU).comp (M.inclusionAlgebraMap hST) =
      M.inclusionAlgebraMap (hST.trans hTU) := by
  ext x
  apply M.realization_injective U
  change M.realization U (M.inclusionAlgebraMap hTU (M.inclusionAlgebraMap hST x)) = _
  rw [M.realization_inclusion, M.realization_inclusion, M.realization_inclusion]
  rw [← Arrows.finiteIntersectionArrow_comp X hST hTU, Affine.OverFunctoriality.affineOverMap_comp]
  rfl

def IntersectionModel.FiniteIntersectionModel.inclusion {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    M.chartScheme T ⟶ M.chartScheme S := M.chartArrow ⟨(S, T), h⟩

instance IntersectionModel.FiniteIntersectionModel.inclusion_open {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    IsOpenImmersion (M.inclusion h) := M.chartArrow_open ⟨(S, T), h⟩

theorem IntersectionModel.FiniteIntersectionModel.inclusion_id (S : Finite.AffineIntersections.finiteIntersectionIndex X) :
    M.inclusion (Finset.Subset.refl S.val) = 𝟙 (M.chartScheme S) := by
  change Spec.map (CommRingCat.ofHom (M.inclusionAlgebraMap _).toRingHom) = _
  rw [M.inclusionAlgebraMap_id]
  exact Spec.map_id _

theorem IntersectionModel.FiniteIntersectionModel.inclusion_comp {S T U : Finite.AffineIntersections.finiteIntersectionIndex X}
    (hST : S.val ⊆ T.val) (hTU : T.val ⊆ U.val) :
    M.inclusion hTU ≫ M.inclusion hST = M.inclusion (hST.trans hTU) := by
  change Spec.map (CommRingCat.ofHom (M.inclusionAlgebraMap hTU).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (M.inclusionAlgebraMap hST).toRingHom) =
    Spec.map (CommRingCat.ofHom (M.inclusionAlgebraMap (hST.trans hTU)).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun f : M.algebra S →ₐ[M.coefficients] M.algebra U =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (M.inclusionAlgebraMap_comp hST hTU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
