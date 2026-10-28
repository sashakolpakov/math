import OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential

/-! # Product Homeomorph Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions

noncomputable section

/-! The actual homeomorphism between a product restricted over a base open and the product with that open is holomorphic in both inherited product manifolds. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N G F : Type} [TopologicalSpace N]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance (priority := low) : ChartedSpace (G × F) (N × F) := prodChartedSpace G N F F

def productBaseOpen (U : Opens N) : Opens (N × F) := ⟨Prod.fst ⁻¹' (U : Set N), U.isOpen.preimage continuous_fst⟩

def openBaseProductHomeomorph (U : Opens N) : productBaseOpen (F := F) U ≃ₜ (U × F) :=
  GraphBaseRestriction.Constructions.baseProductHomeomorph (U : Set N)

theorem baseProductHomeomorph_analytic (U : Opens N) :
    letI : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
    ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G × F) ω
      (openBaseProductHomeomorph (F := F) U) := by
  let : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
  have hv : ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G × F) ω
      (Subtype.val : productBaseOpen (F := F) U → N × F) := contMDiff_subtype_val
  have ha : ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G) ω
      (fun z : productBaseOpen (F := F) U => (⟨z.val.1, z.property⟩ : U)) := by
    apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U _ ω).mp
    rw [modelWithCornersSelf_prod] at hv ⊢
    exact contMDiff_fst.comp hv
  have hb : ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, F) ω
      (fun z : productBaseOpen (F := F) U => z.val.2) := by
    rw [modelWithCornersSelf_prod] at hv ⊢
    exact contMDiff_snd.comp hv
  rw [modelWithCornersSelf_prod]
  exact ha.prodMk hb

theorem baseProductHomeomorph_symm_analytic (U : Opens N) :
    letI : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
    ContMDiff 𝓘(ℂ, G × F) 𝓘(ℂ, G × F) ω
      (openBaseProductHomeomorph (F := F) U).symm := by
  let : ChartedSpace (G × F) (U × F) := prodChartedSpace G U F F
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (productBaseOpen (F := F) U) _ ω).mp
  simp only [modelWithCornersSelf_prod]
  exact (show ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (Subtype.val : U → N) from contMDiff_subtype_val).prodMap
    (show ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, F) ω (id : F → F) from contMDiff_id)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions
