import OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel

/-! # Ordered Radial Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrderedRadialNaturality

noncomputable section

/-! Radial projection commutes exactly with normalized real linear coordinates.
This proves the compatibility needed to compare actual relative boundaries
with the original complex local-to-sphere map. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalSphereChange_projection (e : E ≃L[ℝ] F) (x : CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal E) :
    CycleClass.Geometric.NormalNormChange.Cycles.normalSphereChange e (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection E x) =
      CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection F (CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph e x) := by
  apply Subtype.ext
  rw [CycleClass.Geometric.NormalNormChange.Cycles.normalSphereChange_apply_coe, CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe, CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection_coe]
  change ‖e (‖x.val‖⁻¹ • x.val)‖⁻¹ • e (‖x.val‖⁻¹ • x.val) = ‖e x.val‖⁻¹ • e x.val
  have hn : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
  rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    mul_inv_rev, inv_inv, smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]

theorem normalSphereChange_projection_maps (e : E ≃L[ℝ] F) :
    TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection E) ≫ TopCat.ofHom (CycleClass.Geometric.NormalNormChange.Cycles.normalSphereChange e).toFun =
      TopCat.ofHom ⟨CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph e, (CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph e).continuous⟩ ≫
        TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection F) := by
  apply TopCat.ext
  intro x
  exact normalSphereChange_projection e x

theorem complexNormalLocalRealSphereIso_ordered (p n : ℕ) (hn : n ≠ 0) :
    (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso p n hn).hom =
      CycleClass.Geometric.RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin p → ℂ)) ({0}ᶜ) n ≫
        CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom ⟨CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealPuncturedHomeomorph p,
            (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealPuncturedHomeomorph p).continuous⟩) n ≫
        CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p))))) n := by
  rw [CycleClass.Geometric.RealComplexNormalModel.Cycles.complexNormalLocalRealSphereIso_hom]
  congr 1
  unfold CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap
  rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
    ← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) n)
    (normalSphereChange_projection_maps (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv p))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrderedRadialNaturality
