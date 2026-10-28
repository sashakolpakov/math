import OAI.Analysis.PDE.Nonlinear.LocalBootstrap
import OAI.Analysis.PDE.Nonlinear.BanachJet

/-! A genuine closed-domain Hölder jet solving the Moore equation is C³ inside. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

local instance banachBootstrapFirstGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance banachBootstrapFirstSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance banachBootstrapSecondGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance banachBootstrapSecondSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance

theorem moore_C3_of_banach_jet {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hf : ContDiffOn ℝ 2 f Ω)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (banachJetFunction U) x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (banachJetFunction U) x)).PosDef) :
    ContDiffOn ℝ 3 (banachJetFunction U) Ω := by
  exact moore_C3On_of_holder hn hα hα1 (banachJetFunction U) f hΩ
    (banachJetFunction_contDiffOn hΩ U) hf (norm_nonneg U)
    (banachJetFunction_hessian_holder hΩ U) hPDE hPD

end OAI.Analysis.PDE.Nonlinear
