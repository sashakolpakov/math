import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.HomologySquare

/-! # Projection Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ProjectionCoefficients

noncomputable section

/-! Exact coefficient change preserves the original ordinary-to-ordered
Čech projection, with the finite ordinary coefficient coordinates and
the original ordered coefficient coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uA vA uB vB
variable {C : Type} [Preorder C] [HasFiniteProducts C]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  [HasFiniteBiproducts A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{0,0} G]

omit [HasProducts A] [HasProducts B] [PreservesLimitsOfSize.{0, 0, vA, vB, uA, uB} G] in
private theorem finite_total_iso
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G K = AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G K := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

def ordinaryIso (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :=
  GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso G (NonemptyCechNerve.nerve U)
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) K

omit [LinearOrder ι] [HasCoproducts A] [HasFiniteBiproducts A] [HasCoproducts B] [PreservesLimitsOfSize.{0, 0, vA, vB, uA, uB} G] in
private theorem full_projection (P : Cᵒᵖ ⥤ A) (n : ℕ) (a : Fin (n+1) → ι) :
    ((GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (NonemptyCechNerve.nerve U)
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) P).hom.f n) ≫
        Cech.TupleRestrictionFunctor.projection U (P ⋙ G) a =
      G.map (Cech.TupleRestrictionFunctor.projection U P a) := by
  rw [GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f]
  exact piComparison_comp_π G _ a

omit [Finite ι] [HasCoproducts A] [HasFiniteBiproducts A] [HasCoproducts B] in
private theorem ordered_projection (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (a : Projection.Index (ι := ι) n) :
    ((CoefficientChange.complexIso U G P).hom.f n) ≫
        Projection.projection U (P ⋙ G) n a =
      G.map (Projection.projection U P n a) :=
  piComparison_comp_π G _ a

omit [HasCoproducts A] [HasFiniteBiproducts A] [HasCoproducts B] in
theorem complex_natural (P : Cᵒᵖ ⥤ A) :
    (G.mapHomologicalComplex (.up ℕ)).map (Projection.map U P) ≫
      (CoefficientChange.complexIso U G P).hom =
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (NonemptyCechNerve.nerve U)
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) P).hom ≫
        Projection.map U (P ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Pi.hom_ext
  intro (a : Projection.Index (ι := ι) n)
  change (G.map (Projection.mapF U P n) ≫
      ((CoefficientChange.complexIso U G P).hom.f n)) ≫
      Projection.projection U (P ⋙ G) n a =
    (((GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso G (NonemptyCechNerve.nerve U)
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) P).hom.f n) ≫
        Projection.mapF U (P ⋙ G) n) ≫
      Projection.projection U (P ⋙ G) n a
  rw [Category.assoc, ordered_projection, ← G.map_comp,
    Projection.mapF_projection, Category.assoc,
    Projection.mapF_projection, full_projection]

variable (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

omit [HasCoproducts A] [HasFiniteBiproducts A] [HasCoproducts B] in
theorem bicomplex_natural :
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (TotalProjection.bicomplexMap U K) ≫
      (CoefficientTotal.bicomplexIso U G K).hom =
    (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G (NonemptyCechNerve.nerve U)
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) K).hom ≫
        TotalProjection.bicomplexMap U (CoefficientTotal.mapped G K) := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact complex_natural U G (K.X q)

theorem total_natural :
    (G.mapHomologicalComplex (.up ℕ)).map (TotalProjection.map U K) ≫
      (CoefficientTotal.totalIso U G K).hom =
    (ordinaryIso U G K).hom ≫
      TotalProjection.map U (CoefficientTotal.mapped G K) := by
  have h := IntegralComparison.Finite.TotalCoefficientSquare.comparison G
    (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G (NonemptyCechNerve.nerve U)
      (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) K)
    (CoefficientTotal.bicomplexIso U G K)
    (TotalProjection.bicomplexMap U K)
    (TotalProjection.bicomplexMap U (CoefficientTotal.mapped G K))
    (bicomplex_natural U G K)
  simpa only [IntegralComparison.Finite.TotalCoefficientSquare.iso, ordinaryIso,
    GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.totalIso, finite_total_iso,
    CoefficientTotal.totalIso, TotalProjection.map] using h

def ordinaryHomologyIso [G.PreservesHomology] (q : ℕ) :=
  Functor.HomologySquare.iso G (ordinaryIso U G K) q

theorem homology_natural [G.PreservesHomology] (q : ℕ) :
    G.map (homologyMap (TotalProjection.map U K) q) ≫
      (CoefficientTotal.homologyIso U G K q).hom =
    (ordinaryHomologyIso U G K q).hom ≫
      homologyMap (TotalProjection.map U (CoefficientTotal.mapped G K)) q :=
  Functor.HomologySquare.naturality G (TotalProjection.map U K)
    (TotalProjection.map U (CoefficientTotal.mapped G K))
    (ordinaryIso U G K) (CoefficientTotal.totalIso U G K)
    (total_natural U G K) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ProjectionCoefficients
