import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Naturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap

/-! # Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement

noncomputable section

/-! Refinement on ordered Čech complexes is the original full refinement
between signed-sorting inclusion and ordered projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

def transformation : Functor.Projection.functor U (D := D) ⟶
    Functor.Projection.functor V (D := D) :=
  Naturality.inclusionTransformation U ≫
    GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.transformation U V r ≫
    Naturality.projectionTransformation V

def map (P : Cᵒᵖ ⥤ D) : Projection.complex U P ⟶
    Projection.complex V P := (transformation U V r).app P

omit [HasCoproducts D] in
theorem map_eq (P : Cᵒᵖ ⥤ D) : Refinement.map U V r P =
    Retraction.inclusion U P ≫
      GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P ≫
        Projection.map V P := rfl

omit [LinearOrder ι] [LinearOrder κ] in
omit [HasCoproducts D] in
theorem full_refinement (P : Cᵒᵖ ⥤ D) :
    GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P =
      GeometricComparison.Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V) r P := rfl

omit [HasCoproducts D] in
theorem projection_quasiIso (P : Cᵒᵖ ⥤ D) : QuasiIso (Projection.map U P) := by
  rw [_root_.quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact inferInstanceAs (IsIso ((Homotopy.equiv U P).toHomologyIso n).hom)

omit [HasCoproducts D] in
theorem inclusion_quasiIso (P : Cᵒᵖ ⥤ D) : QuasiIso (Retraction.inclusion U P) := by
  rw [_root_.quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact inferInstanceAs (IsIso ((Homotopy.equiv U P).toHomologyIso n).inv)

omit [HasCoproducts D] in
theorem quasiIso (P : Cᵒᵖ ⥤ D)
    [QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P)] : QuasiIso (Refinement.map U V r P) := by
  let : QuasiIso (Projection.map V P) := projection_quasiIso V P
  let : QuasiIso (Retraction.inclusion U P) := inclusion_quasiIso U P
  rw [map_eq]
  infer_instance

def bicomplexMap (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) :
    ((Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((Functor.Projection.functor V).mapHomologicalComplex (.up ℕ)).obj K :=
  (NatTrans.mapHomologicalComplex (transformation U V r) (.up ℕ)).app K

def totalMap (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap U V r K) (.up ℕ)

theorem total_quasiIso {R : Type v} [Ring R]
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ)
    (hK : ∀ q, QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (K.X q))) :
    QuasiIso (totalMap U V r K) := by
  apply AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns
  intro q
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (K.X q)) := hK q
  exact quasiIso U V r (K.X q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement
