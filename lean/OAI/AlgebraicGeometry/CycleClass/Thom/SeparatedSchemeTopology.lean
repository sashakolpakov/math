import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Metrizable.Urysohn

/-! # Separated Scheme Topology -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SeparatedSchemeTopology.Constructions

noncomputable section

/-! Separated finite-type complex schemes have Hausdorff, metrizable
ordinary point spaces, via the actual diagonal and affine point topology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SchemeProper.Constructions

theorem schemePoints_t2 (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  let d : X ⟶ X ⊗ X := lift (𝟙 X) (𝟙 X)
  let : IsClosedImmersion d.left := by
    change IsClosedImmersion (CategoryTheory.Limits.pullback.diagonal X.hom)
    infer_instance
  let : LocallyOfFiniteType (X ⊗ X).hom :=
    inferInstanceAs (LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.fst X.hom X.hom ≫ X.hom))
  let e := Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X
  have hp := e.isProperMap.comp (Integral.SchemeProper.Constructions.isProperMap_integral d)
  have he : e ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map d = fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => (x, x) := by
    funext x
    change ((x ≫ d) ≫ fst X X, (x ≫ d) ≫ snd X X) = (x, x)
    simp only [d, Category.assoc, lift_fst, lift_snd, Category.comp_id]
  apply t2_iff_isClosed_diagonal.mpr
  have hr : Set.range (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => (x, x)) =
      Set.diagonal (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro h
      exact ⟨p.1, Prod.ext rfl h⟩
  rw [← hr, ← he]
  exact hp.isClosed_range

theorem schemePoints_metrizable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  let : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := schemePoints_t2 X
  let : LocallyCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_locallyCompact X
  let : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X
  infer_instance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SeparatedSchemeTopology.Constructions
