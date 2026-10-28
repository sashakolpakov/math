import OAI.AlgebraicGeometry.Cycles.Functoriality.Covering
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.OpenFundamental

/-! # Local Orientation -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.LocalOrientation.Construction

noncomputable section

section

open scoped _root_.Manifold ContDiff
open _root_.CategoryTheory _root_.TopologicalSpace

section Partial

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]

def analyticPartialSource (e : PartialDiffeomorph (𝓘(ℂ, E)) (𝓘(ℂ, F)) M N ω) :
    Opens M := ⟨e.source, e.open_source⟩

def analyticPartialTarget (e : PartialDiffeomorph (𝓘(ℂ, E)) (𝓘(ℂ, F)) M N ω) :
    Opens N := ⟨e.target, e.open_target⟩

/-- A partial analytic diffeomorphism restricts to a genuine complex
C1 diffeomorphism between its open source and target. -/
def analyticPartialSourceTarget
    (e : PartialDiffeomorph (𝓘(ℂ, E)) (𝓘(ℂ, F)) M N ω) :
    Diffeomorph (𝓘(ℂ, E)) (𝓘(ℂ, F)) (analyticPartialSource e) (analyticPartialTarget e) 1 := by
  let h : analyticPartialSource e ≃ₜ analyticPartialTarget e :=
    e.toOpenPartialHomeomorph.toHomeomorphSourceTarget
  have hf : ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, F)) ∞ h := by
    apply (ContMDiff.subtypeVal_comp_iff (analyticPartialTarget e) h).mp
    intro x
    change ContMDiffAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) ∞
      (fun z : analyticPartialSource e => e z.val) x
    apply contMDiffAt_subtype_iff.mpr
    exact (e.contMDiffOn_toFun.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)).contMDiffAt
      (e.open_source.mem_nhds x.property)
  have hi : ContMDiff (𝓘(ℂ, F)) (𝓘(ℂ, E)) ∞ h.symm := by
    apply (ContMDiff.subtypeVal_comp_iff (analyticPartialSource e) h.symm).mp
    intro x
    change ContMDiffAt (𝓘(ℂ, F)) (𝓘(ℂ, E)) ∞
      (fun z : analyticPartialTarget e => e.invFun z.val) x
    apply contMDiffAt_subtype_iff.mpr
    exact (e.contMDiffOn_invFun.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)).contMDiffAt
      (e.open_target.mem_nhds x.property)
  exact { __ := h
          contMDiff_toFun := hf.of_le (by simp)
          contMDiff_invFun := hi.of_le (by simp) }

end Partial

variable (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]

def analyticPartialSourceMap
    (e : PartialDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) M N ω) :
    TopCat.of (analyticPartialSource e) ⟶ TopCat.of N :=
  (TopCat.isoOfHomeo (X := TopCat.of (analyticPartialSource e))
    (Y := TopCat.of (analyticPartialTarget e))
    e.toOpenPartialHomeomorph.toHomeomorphSourceTarget).hom ≫
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (analyticPartialTarget e : Set N)

theorem analyticPartialSourceMap_injective
    (e : PartialDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) M N ω) :
    Function.Injective (analyticPartialSourceMap d e) := by
  intro x y hxy
  exact Subtype.ext (e.toPartialEquiv.injOn x.property y.property hxy)

variable [T2Space M] [T2Space N]
variable [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 N]

/-- Every analytic local sheet preserves the canonical complex local
generator on its open source. -/
theorem complexCanonicalLocalClass_partialSourceMap
    (e : PartialDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) M N ω)
    (x : analyticPartialSource e) :
    CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap (X := TopCat.of (analyticPartialSource e))
      (Y := TopCat.of N) (analyticPartialSourceMap d e)
      (analyticPartialSourceMap_injective d e) x (2 * d)
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := analyticPartialSource e) x) =
    CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (e x.val) := by
  let h := analyticPartialSourceTarget e
  let i : TopCat.of (analyticPartialTarget e) ⟶ TopCat.of N :=
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (analyticPartialTarget e : Set N)
  let j : TopCat.of (analyticPartialSource e) ⟶ TopCat.of (analyticPartialTarget e) :=
    (TopCat.isoOfHomeo (X := TopCat.of (analyticPartialSource e))
      (Y := TopCat.of (analyticPartialTarget e)) h.toHomeomorph).hom
  have hj : Function.Injective j := h.toHomeomorph.injective
  have hcomp := CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap_comp j i hj Subtype.val_injective x (2 * d)
  have hd := CycleClass.Geometric.ComplexFundamentalNaturality.Cycles.complexCanonicalLocalClass_diffeomorph h x
  have hi := CycleClass.Geometric.ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := d) (analyticPartialTarget e) (h x)
  exact (ConcreteCategory.congr_hom hcomp
    (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := analyticPartialSource e) x)).symm.trans
      ((congrArg (CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective (h x) (2 * d)) hd).trans hi)

/-- The same orientation identity with a specified target point. -/
theorem complexCanonicalLocalClass_partialSourceMap_to
    (e : PartialDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) M N ω)
    (x : analyticPartialSource e) (y : N) (hxy : e x.val = y) :
    CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMapTo (analyticPartialSourceMap d e)
      (analyticPartialSourceMap_injective d e) x y hxy (2 * d)
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := analyticPartialSource e) x) =
    CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y := by
  subst y
  exact complexCanonicalLocalClass_partialSourceMap d e x

end

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (d : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin d → ℂ) N]
variable [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 N]

/-- An injective analytic local diffeomorphism preserves each canonical
complex local orientation class, even when its image is not the entire target. -/
theorem complexCanonicalLocalClass_injective_localDiffeomorph
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f) (x : M) :
    CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * d) (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) =
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (f x) := by
  obtain ⟨e, hx, he⟩ := hl x
  let U := analyticPartialSource e
  let x' : U := ⟨x, hx⟩
  let i : TopCat.of U ⟶ TopCat.of M := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)
  have hi : Set.MapsTo i ({x'} : Set U)ᶜ ({x} : Set M)ᶜ := by
    intro y hy heq
    exact hy (Subtype.ext heq)
  have hf' : Set.MapsTo f ({x} : Set M)ᶜ ({f x} : Set N)ᶜ := by
    intro y hy heq
    exact hy (hf heq)
  have hfe : i ≫ f = analyticPartialSourceMap d e := by
    ext z
    exact he z.property
  have hmaps : CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d) ≫
      CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * d) =
    CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMapTo (analyticPartialSourceMap d e)
      (analyticPartialSourceMap_injective d e) x' (f x) (he hx).symm (2 * d) :=
    (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp i f hi hf' (2 * d)).trans
      (CycleClass.Geometric.LocalChartMaps.Cycles.relativeSingularHomologyMap_congr hfe _ _ (2 * d))
  have h := ConcreteCategory.congr_hom hmaps (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x')
  have ho : CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d)
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x') = CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x :=
    CycleClass.Geometric.ComplexOpenOrientation.Cycles.complexCanonicalLocalClass_open_inclusion (p := d) U x'
  change CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap f hf x (2 * d)
      (CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap i Subtype.val_injective x' (2 * d)
        (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x')) = _ at h
  rw [ho] at h
  exact h.trans (complexCanonicalLocalClass_partialSourceMap_to d e x' (f x) (he hx).symm)

/-- Consequently an injective analytic local diffeomorphism preserves
the actual compact-support fundamental class on every compact set. -/
theorem complexCompactFundamentalClass_injective_localDiffeomorph
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin d → ℂ)) ω f)
    (K : Set M) (hK : IsCompact K) :
    CycleClass.Geometric.OpenFundamental.Cycles.injectiveSupportHomologyMap f hf K (2 * d) (CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK) =
      CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (f '' K) (hK.image f.hom.continuous) :=
  CycleClass.Geometric.OpenFundamental.Cycles.complexCompactFundamentalClass_map_of_local d f hf
    (complexCanonicalLocalClass_injective_localDiffeomorph d f hf hl) K hK

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.LocalOrientation.Construction
