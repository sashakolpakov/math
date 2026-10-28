import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.AutomorphyBundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-! # Automorphy Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Automorphic holomorphic functions give sections of the actual line bundle. -/

open _root_.Topology Filter Bundle
open scoped _root_.Manifold ContDiff

variable {Φ : Torus.Data.CM.ProjectivePeriodData} (J : Φ.AutomorphyFactor)

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.power (n : ℕ) : Φ.AutomorphyFactor where
  value l z := J.value l z ^ n
  zero z := by rw [J.zero, one_pow]
  add l m z := by rw [J.add, mul_pow]
  continuous l := (J.continuous l).pow n

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.sectionValue (s : Φ.space → ℂ) (q : Φ.periodTorus) : J.vectorBundleCore.Fiber q :=
  s (Φ.periodChart q q)

variable (s : Φ.space → ℂ)
  (hs : ∀ l : Φ.periodIntegerLattice, ∀ z, s (z + l.val) = J.value l z * s z)

include hs

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.sectionValue_in_frame (i q : Φ.periodTorus) (hq : q ∈ (Φ.periodChart i).source) :
    ((J.vectorBundleCore.localTriv i) ⟨q, J.sectionValue s q⟩).2 = s (Φ.periodChart i q) := by
  change J.value (Φ.periodChartDifference q i q) (Φ.periodChart q q) *
    s (Φ.periodChart q q) = s (Φ.periodChart i q)
  have ht := hs (Φ.periodChartDifference q i q) (Φ.periodChart q q)
  have hshift : Φ.periodChart q q + (Φ.periodChartDifference q i q).val = Φ.periodChart i q := by
    rw [Φ.periodChartDifference_val q i q ⟨Φ.mem_periodChart_source q, hq⟩]
    abel
  exact ht.symm.trans (congrArg s hshift)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.sectionValue_contMDiff [J.vectorBundleCore.IsContMDiff 𝓘(ℂ, Φ.space) ∞]
    (hreg : ContDiff ℂ ∞ s) :
    ContMDiff 𝓘(ℂ, Φ.space) (𝓘(ℂ, Φ.space).prod 𝓘(ℂ, ℂ)) ∞
      (fun q => (⟨q, J.sectionValue s q⟩ : J.vectorBundleCore.TotalSpace)) := by
  intro q
  rw [contMDiffAt_section]
  have hc : ContMDiffAt 𝓘(ℂ, Φ.space) 𝓘(ℂ, Φ.space) ∞ (Φ.periodChart q) q := by
    have h := contMDiffAt_extChartAt' (I := 𝓘(ℂ, Φ.space)) (x := q) (n := ∞)
      (Φ.mem_periodChart_source q)
    simpa only [Φ.period_extChart] using h
  apply ((hreg.contMDiff.contMDiffAt).comp q hc).congr_of_eventuallyEq
  filter_upwards [(Φ.periodChart q).open_source.mem_nhds (Φ.mem_periodChart_source q)] with t ht
  exact J.sectionValue_in_frame s hs q t ht

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.holomorphicSection [J.vectorBundleCore.IsContMDiff 𝓘(ℂ, Φ.space) ∞]
    (hreg : ContDiff ℂ ∞ s) :
    ContMDiffSection 𝓘(ℂ, Φ.space) ℂ ∞ J.vectorBundleCore.Fiber where
  toFun := J.sectionValue s
  contMDiff_toFun := J.sectionValue_contMDiff s hs hreg

end

end OAI.RepresentationTheory.Theta.Geometric
