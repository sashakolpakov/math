import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.FormalCoproductQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap

/-! # Presheaf Cech Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.PresheafCechQuasiIso

noncomputable section

/-! Ordinary ordered Cech totals preserve maps that are quasi-isomorphisms
on all nonempty formal intersections of their cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
universe u
variable (R : Type u) [CommRing R] {X : TopCat.{u}}
  {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ} (a : K ⟶ L)

def bicomplexMap := ((OrderedCech.Functor.Projection.functor V).mapHomologicalComplex (.up ℕ)).map a

theorem column_quasiIso (p : ℕ)
    (ha : ∀ j : AugmentedOrdered.Cech.Index ι (p+1), QuasiIso
      ((((CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj
        (op ((AugmentedOrdered.Cech.formal V (p+1)).obj j))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso ((GeometricComparison.TotalFlip.TotalFlipNaturality.flipped (bicomplexMap R V a)).f p) :=
  FormalCoproductQuasiIso.quasiIso R (AugmentedOrdered.Cech.formal V (p+1)) a ha

theorem quasiIso_of_evaluation
    (ha : ∀ p (j : AugmentedOrdered.Cech.Index ι (p+1)), QuasiIso
      ((((CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj
        (op ((AugmentedOrdered.Cech.formal V (p+1)).obj j))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso ((Presheaf.OrderedCover.Comparison.totalFunctor V).map a) := by
  let : QuasiIso (HomologicalComplex₂.total.map
      (GeometricComparison.TotalFlip.TotalFlipNaturality.flipped (bicomplexMap R V a)) (.up ℕ)) :=
    AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns _
      (fun p => column_quasiIso R V a p (ha p))
  constructor
  intro n
  exact (GeometricComparison.TotalFlip.TotalFlipNaturality.quasiIsoAt_iff (bicomplexMap R V a) n).mp inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.PresheafCechQuasiIso
