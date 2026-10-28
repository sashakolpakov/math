import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorPairwiseLimits

/-! # Cover Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoverTensorComparison

noncomputable section

/-! A tensor comparison that is an isomorphism on a finite cover and its overlaps
is an isomorphism on the union. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

variable {X : TopCat.{u}} {R : Type u} [CommRing R]

theorem finiteCoverTensorComparison_isIso
    (F G : TopCat.Presheaf (ModuleCat.{u} R) X) (hF : F.IsSheaf) (hG : G.IsSheaf)
    (N : ModuleCat.{u} R) [Module.Flat R N] (α : F ⋙ tensorLeft N ⟶ G)
    {ι : Type u} [Finite ι] (U : ι → TopologicalSpace.Opens X)
    (hα : ∀ i : Pairwise ι, IsIso (α.app (.op ((Pairwise.diagram U).obj i)))) :
    IsIso (α.app (.op (iSup U))) := by
  classical
  let := Fintype.ofFinite ι
  let C := (Pairwise.cocone U).op
  let β := CategoryTheory.Functor.whiskerLeft (Pairwise.diagram U).op α
  have : ∀ i, IsIso (β.app i) := fun i => hα i.unop
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let e := asIso β
  let c := (tensorLeft N).mapCone (F.mapCone C)
  let d := G.mapCone C
  have hc : IsLimit c :=
    isLimitOfPreserves (tensorLeft N) (Classical.choice (hF.isSheafPairwiseIntersections U))
  have hd : IsLimit d := Classical.choice (hG.isSheafPairwiseIntersections U)
  let k : (Cone.postcompose e.hom).obj c ⟶ d := {
    hom := α.app (.op (iSup U))
    w := fun i => (α.naturality (C.π.app i)).symm }
  have : IsIso k := ((IsLimit.postcomposeHomEquiv e c).symm hc).hom_isIso hd k
  exact (Cone.forget _).map_isIso k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoverTensorComparison
