import OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SimpleZero
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.InverseChartChange

/-! # Product Simple Zero -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductSimpleZero.Constructions.Class

noncomputable section

/-! Simple-zero normalization on open subsets of an actual normal product, in its specified complex chart. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions.Product OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.FinitePointProjection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SimpleZero.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Local.InverseChartChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions

variable {p d : ℕ} (U : Opens (Fin p → ℂ)) [Nonempty U]
  (e : ((Fin p → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (p + d) → ℂ))

local instance (priority := low) : ChartedSpace ((Fin p → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin p → ℂ) U (Fin d → ℂ) (Fin d → ℂ)

def localPointClass (V : Opens (U × (Fin d → ℂ))) (z : V) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) ({z}ᶜ) (2 * (p + d)) :=
  letI := FinitePointProjection.Constructions.Product.openProductCharted U e
  CanonicalLocalDual.Constructions.canonicalLocalDual (p + d) z

theorem simpleZero_class (q : U × (Fin d → ℂ) → (Fin (p + d) → ℂ))
    (V : Opens (U × (Fin d → ℂ))) (z : V)
    (hq : IsLocalDiffeomorphAt 𝓘(ℂ, (Fin p → ℂ) × (Fin d → ℂ))
      𝓘(ℂ, Fin (p + d) → ℂ) ω q z.val)
    (g : TopCat.of V ⟶ TopCat.of (Fin (p + d) → ℂ))
    (hg : (g : V → (Fin (p + d) → ℂ)) = q ∘ Subtype.val)
    (hz : g z = 0) (hp : Set.MapsTo g ({z}ᶜ) ({0}ᶜ)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hp (2 * (p + d))
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + d)) = localPointClass U e V z := by
  have hc := Local.InverseChartChange.Constructions.localInverse_in_embedding_chart (p + d) (ProductCoordinates.Constructions.flatOpenCoordinate U e)
    (ProductCoordinates.Constructions.flatOpenCoordinate_isOpenEmbedding U e) q z.val (ProductCoordinates.Constructions.flatOpenCoordinate_localInverse U e z.val) hq
  let := FinitePointProjection.Constructions.Product.openProductCharted U e
  let := FinitePointProjection.Constructions.openProductManifold U e
  exact SimpleZero.Constructions.Class.simpleZero_class (p + d) q V z hc g hg hz hp

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductSimpleZero.Constructions.Class
