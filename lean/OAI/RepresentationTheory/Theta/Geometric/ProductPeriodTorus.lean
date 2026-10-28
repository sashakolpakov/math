import OAI.RepresentationTheory.Theta.Geometric.ProductPeriodData
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold

/-! # Product Period Torus -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The quotient by the product lattice is the actual product of period tori. -/

open scoped _root_.Manifold ContDiff

variable (Φ Ψ : Torus.Data.CM.ProjectivePeriodData)

def Torus.Data.CM.ProjectivePeriodData.productTorusEquiv : (Φ.product Ψ).periodTorus ≃+ Φ.periodTorus × Ψ.periodTorus :=
  QuotientAddGroup.prodAddEquiv Φ.periodIntegerLattice.toAddSubgroup Ψ.periodIntegerLattice.toAddSubgroup

@[simp] theorem Torus.Data.CM.ProjectivePeriodData.productTorusEquiv_mk (z : Φ.space × Ψ.space) :
    Φ.productTorusEquiv Ψ (QuotientAddGroup.mk z) =
      (QuotientAddGroup.mk z.1, QuotientAddGroup.mk z.2) := rfl

@[simp] theorem Torus.Data.CM.ProjectivePeriodData.productTorusEquiv_symm_mk (u : Φ.space) (v : Ψ.space) :
    (Φ.productTorusEquiv Ψ).symm (QuotientAddGroup.mk u, QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (u, v) := by
  apply (Φ.productTorusEquiv Ψ).injective
  rw [AddEquiv.apply_symm_apply]
  exact (Φ.productTorusEquiv_mk Ψ (u, v)).symm

theorem Torus.Data.CM.ProjectivePeriodData.productTorusEquiv_continuous : Continuous (Φ.productTorusEquiv Ψ) := by
  apply continuous_quot_lift
  exact (QuotientAddGroup.continuous_mk.comp continuous_fst).prodMk
    (QuotientAddGroup.continuous_mk.comp continuous_snd)

def Torus.Data.CM.ProjectivePeriodData.productTorusHomeomorph : (Φ.product Ψ).periodTorus ≃ₜ Φ.periodTorus × Ψ.periodTorus :=
  (Φ.productTorusEquiv Ψ).toEquiv.toHomeomorphOfContinuousClosed
    (Φ.productTorusEquiv_continuous Ψ) (Φ.productTorusEquiv_continuous Ψ).isClosedMap

theorem Torus.Data.CM.ProjectivePeriodData.productTorusEquiv_contMDiff :
    ContMDiff 𝓘(ℂ, (Φ.product Ψ).space) (𝓘(ℂ, Φ.space).prod 𝓘(ℂ, Ψ.space)) ∞
      (Φ.productTorusEquiv Ψ) := by
  apply ContMDiff.prodMk
  · apply (Φ.product Ψ).contMDiff_of_periodProjection
    let f : (Φ.product Ψ).space →L[ℂ] Φ.space := ContinuousLinearMap.fst ℂ Φ.space Ψ.space
    exact Φ.periodProjection_contMDiff.comp f.contDiff.contMDiff
  · apply (Φ.product Ψ).contMDiff_of_periodProjection
    let f : (Φ.product Ψ).space →L[ℂ] Ψ.space := ContinuousLinearMap.snd ℂ Φ.space Ψ.space
    exact Ψ.periodProjection_contMDiff.comp f.contDiff.contMDiff

theorem Torus.Data.CM.ProjectivePeriodData.productTorusEquiv_symm_contMDiff :
    ContMDiff (𝓘(ℂ, Φ.space).prod 𝓘(ℂ, Ψ.space)) 𝓘(ℂ, (Φ.product Ψ).space) ∞
      (Φ.productTorusEquiv Ψ).symm := by
  intro p
  apply contMDiffAt_iff_source.mpr
  let e : (Φ.space × Ψ.space) →L[ℂ] (Φ.product Ψ).space := ContinuousLinearMap.id ℂ _
  have hf := (Φ.product Ψ).periodProjection_contMDiff.comp e.contDiff.contMDiff
  change ContMDiff 𝓘(ℂ, Φ.space × Ψ.space) 𝓘(ℂ, (Φ.product Ψ).space) ∞
    (fun z : Φ.space × Ψ.space => (QuotientAddGroup.mk (z.1, z.2) : (Φ.product Ψ).periodTorus)) at hf
  simp only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
    Φ.period_extChart_symm, Ψ.period_extChart_symm, Function.comp_def,
    Torus.Data.CM.ProjectivePeriodData.productTorusEquiv_symm_mk]
  exact (hf ((extChartAt 𝓘(ℂ, Φ.space) p.1) p.1,
    (extChartAt 𝓘(ℂ, Ψ.space) p.2) p.2)).contMDiffWithinAt

def Torus.Data.CM.ProjectivePeriodData.productTorusDiffeomorph : (Φ.product Ψ).periodTorus ≃ₘ⟮𝓘(ℂ, (Φ.product Ψ).space),
    𝓘(ℂ, Φ.space).prod 𝓘(ℂ, Ψ.space)⟯ Φ.periodTorus × Ψ.periodTorus where
  toEquiv := (Φ.productTorusEquiv Ψ).toEquiv
  contMDiff_toFun := Φ.productTorusEquiv_contMDiff Ψ
  contMDiff_invFun := Φ.productTorusEquiv_symm_contMDiff Ψ

end

end OAI.RepresentationTheory.Theta.Geometric
