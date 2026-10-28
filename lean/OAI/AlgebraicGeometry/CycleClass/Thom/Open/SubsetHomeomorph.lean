import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement

/-! # Subset Homeomorph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions

noncomputable section

/-! For two nested ambient opens, the actual smaller open is holomorphically identical with its preimage inside the larger open. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N G : Type} [TopologicalSpace N]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (U P : Opens N) (hP : P ≤ U)

def insideOpen : Opens U := ⟨Subtype.val ⁻¹' (P : Set N), P.isOpen.preimage continuous_subtype_val⟩

def smallerOpenHomeomorph : insideOpen U P ≃ₜ P where
  toFun x := ⟨x.val.val, x.property⟩
  invFun y := ⟨⟨y.val, hP y.property⟩, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem smallerOpenHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (smallerOpenHomeomorph U P hP) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff P _ ω).mp
  exact (show ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (Subtype.val : U → N) from contMDiff_subtype_val).comp
    (show ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (Subtype.val : insideOpen U P → U) from contMDiff_subtype_val)

theorem smallerOpenHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (smallerOpenHomeomorph U P hP).symm := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (insideOpen U P) _ ω).mp
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U _ ω).mp
  exact (show ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, G) ω (Subtype.val : P → N) from contMDiff_subtype_val)

def smallerOpenMap : TopCat.of P ⟶ TopCat.of U :=
  ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (insideOpen U P) (smallerOpenHomeomorph U P hP)

theorem smallerOpenMap_comp : smallerOpenMap U P hP ≫ Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N) =
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (P : Set N) := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions
