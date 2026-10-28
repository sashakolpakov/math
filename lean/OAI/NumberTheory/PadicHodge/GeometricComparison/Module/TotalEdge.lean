import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalEdge
import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Total Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalEdge.ModuleTotalEdge

noncomputable section

/-! Exact augmented rows of module complexes give the canonical
quasi-isomorphism to their actual total complex in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable (R : Type u) [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ))
  (K : CochainComplex (ModuleCat.{max u v} R) ℕ)
  (e : ∀ q, K.X q ⟶ (B.X q).X 0)
  (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' → e q ≫ (B.d q q').f 0 = K.d q q' ≫ e q')
  (hzero : ∀ q, e q ≫ (B.X q).d 0 1 = 0)

local instance hasTotal : B.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts B

theorem quasiIso
    (haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (hzero q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : ∀ q r, (B.X q).ExactAt (r + 1)) :
    QuasiIso ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he hzero) := by
  constructor
  intro n
  cases n with
  | zero => exact AlgebraicGeometry.Comparison.Betti.TotalComplexDegreeZero.horizontal_edge_quasiIsoAt_zero B K e he hzero (haug 0) hmono
  | succ n =>
    let F := forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}
    let : PreservesColimitsOfSize.{max u v, max u v} F := by dsimp only [F]; infer_instance
    let : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
    exact (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
      ((AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge B) K e he hzero) F (n + 1)).mp
        (TotalEdge.TotalEdgeComparison.mapped_edge_quasiIsoAt_succ F B K e he hzero haug hmono hrows n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalEdge.ModuleTotalEdge
