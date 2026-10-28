import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraTensorFunctor

/-! # Algebra Functor Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorModel

noncomputable section

/-! Faithful recovery makes the arrows of a descended algebra diagram satisfy the original functor laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

abbrev SmoothAlgebraFunctorModel
    (R : Type u) [CommRing R] {J : Type v} [Category.{w} J] (A : J ⥤ CommAlgCat.{u} R) :=
  AffineDiagramModel.SmoothAffineDiagramModel R (fun i => ↥(A.obj i))
    (fun k : Σ i j : J, i ⟶ j => k.1) (fun k => k.2.1) (fun k => (A.map k.2.2).hom)

namespace SmoothAlgebraFunctorModel

variable {R : Type u} [CommRing R] {J : Type v} [Category.{w} J]
variable {A : J ⥤ CommAlgCat.{u} R} (M : SmoothAlgebraFunctorModel R A)

theorem arrow_id (i : J) : M.arrow ⟨i, i, 𝟙 i⟩ = AlgHom.id M.coefficients (M.algebra i) := by
  ext x
  apply M.realization_injective i
  rw [M.realization_arrow ⟨i, i, 𝟙 i⟩]
  change (A.map (𝟙 i)).hom (M.realization i x) = M.realization i x
  rw [A.map_id]
  rfl

theorem arrow_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    M.arrow ⟨i, k, f ≫ g⟩ = (M.arrow ⟨j, k, g⟩).comp (M.arrow ⟨i, j, f⟩) := by
  ext x
  apply M.realization_injective k
  change M.realization k (M.arrow ⟨i, k, f ≫ g⟩ x) =
    M.realization k (M.arrow ⟨j, k, g⟩ (M.arrow ⟨i, j, f⟩ x))
  rw [M.realization_arrow ⟨i, k, f ≫ g⟩, M.realization_arrow ⟨j, k, g⟩,
    M.realization_arrow ⟨i, j, f⟩]
  change (A.map (f ≫ g)).hom (M.realization i x) =
    (A.map g).hom ((A.map f).hom (M.realization i x))
  rw [A.map_comp]
  rfl

def algebraFunctor : J ⥤ CommAlgCat.{u} M.coefficients where
  obj i := M.algebra i
  map {i j} f := CommAlgCat.ofHom (M.arrow ⟨i, j, f⟩)
  map_id i := CommAlgCat.hom_ext (M.arrow_id i)
  map_comp f g := CommAlgCat.hom_ext (M.arrow_comp f g)

end SmoothAlgebraFunctorModel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorModel
