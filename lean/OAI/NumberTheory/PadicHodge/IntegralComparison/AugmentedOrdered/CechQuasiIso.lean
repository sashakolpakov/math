import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.FormalCoproductQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap

/-! # Cech Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechQuasiIso

noncomputable section

/-! The original augmented ordered Čech total preserves pointwise
quasi-isomorphisms of actual module-presheaf complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  (R : Type u) [CommRing R]
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ} (a : K ⟶ L)

theorem column_quasiIso (p : ℕ)
    (ha : ∀ i : Cech.Index ι p, QuasiIso
      ((((CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{u} R)).obj
        (op ((Cech.formal U p).obj i))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso ((GeometricComparison.TotalFlip.TotalFlipNaturality.flipped (CechForgetNaturality.bicomplexMap U a)).f p) :=
  FormalCoproductQuasiIso.quasiIso R (Cech.formal U p) a ha

theorem quasiIso_of_evaluation
    (ha : ∀ p (i : Cech.Index ι p), QuasiIso
      ((((CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{u} R)).obj
        (op ((Cech.formal U p).obj i))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (CechForgetNaturality.map U a) := by
  let : QuasiIso (HomologicalComplex₂.total.map
      (GeometricComparison.TotalFlip.TotalFlipNaturality.flipped (CechForgetNaturality.bicomplexMap U a)) (.up ℕ)) :=
    AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns _
      (fun p => column_quasiIso U R a p (ha p))
  constructor
  intro n
  exact (GeometricComparison.TotalFlip.TotalFlipNaturality.quasiIsoAt_iff (CechForgetNaturality.bicomplexMap U a) n).mp inferInstance

theorem quasiIso [QuasiIso a] : QuasiIso (CechForgetNaturality.map U a) :=
  quasiIso_of_evaluation U R a (fun _ _ => inferInstance)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechQuasiIso
