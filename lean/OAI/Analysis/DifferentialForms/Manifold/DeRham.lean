import OAI.Analysis.DifferentialForms.Manifold.SquareZeroD
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # De Rham -/

namespace OAI.Analysis.DifferentialForms.Manifold.DeRham

noncomputable section

/-!
# The complex de Rham complex of a real normed space

Its degree-n terms are actual smooth complex-valued real alternating forms,
and its differential is exterior differentiation. The homology construction is
mathlib's categorical kernel/image construction, identified below with its
explicit module quotient. This is a local model; no comparison with singular
cohomology or global manifold chart-gluing theorem is assumed here.
-/

open _root_.CategoryTheory

universe u
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual de Rham cochain complex with complex coefficients. -/
def deRhamComplex : CochainComplex (ModuleCat.{u} ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (Basic.SmoothForm E n))
    (fun _ => ModuleCat.ofHom Basic.SmoothForm.d)
    (fun n => ModuleCat.hom_ext (Basic.SmoothForm.d_comp_d (E := E) n))

@[simp]
theorem deRhamComplex_X (n : ℕ) :
    (deRhamComplex E).X n = ModuleCat.of ℂ (Basic.SmoothForm E n) := rfl

@[simp]
theorem deRhamComplex_d (n : ℕ) :
    (deRhamComplex E).d n (n + 1) = ModuleCat.ofHom
      (Basic.SmoothForm.d : Basic.SmoothForm E n →ₗ[ℂ] Basic.SmoothForm E (n + 1)) := by
  exact CochainComplex.of_d
    (fun k => ModuleCat.of ℂ (Basic.SmoothForm E k))
    (fun k => ModuleCat.ofHom (Basic.SmoothForm.d :
      Basic.SmoothForm E k →ₗ[ℂ] Basic.SmoothForm E (k + 1))) n

/-- The differential in the assembled complex is the given exterior derivative. -/
@[simp]
theorem deRhamComplex_d_apply (n : ℕ) (ω : Basic.SmoothForm E n) :
    (deRhamComplex E).d n (n + 1) ω = Basic.SmoothForm.d ω := by
  rw [deRhamComplex_d]
  rfl

/-- Complex de Rham cohomology of this normed-space model. -/
def deRhamCohomology (n : ℕ) : ModuleCat.{u} ℂ :=
  (deRhamComplex E).homology n

/-- The module of cocycles in the actual de Rham cochain complex. -/
def deRhamCocycles (n : ℕ) : ModuleCat.{u} ℂ :=
  (deRhamComplex E).cycles n

/-- The canonical complex-linear map sending a closed form to its cohomology class. -/
def deRhamClass (n : ℕ) : deRhamCocycles E n ⟶ deRhamCohomology E n :=
  (deRhamComplex E).homologyπ n

/-- The cocycles are the kernel of the next differential. -/
def deRhamCocyclesKernelIso (n : ℕ) :
    deRhamCocycles E n ≅
      ModuleCat.of ℂ (LinearMap.ker ((deRhamComplex E).sc n).g.hom) :=
  ((deRhamComplex E).sc n).moduleCatCyclesIso

/-- The cohomology is precisely the kernel modulo the incoming image, using
mathlib's explicit module model of the categorical homology construction. -/
def deRhamCohomologyQuotientIso (n : ℕ) :
    deRhamCohomology E n ≅ ModuleCat.of ℂ
      (LinearMap.ker ((deRhamComplex E).sc n).g.hom ⧸
        LinearMap.range ((deRhamComplex E).sc n).moduleCatToCycles) :=
  ((deRhamComplex E).sc n).moduleCatHomologyIso

end

end OAI.Analysis.DifferentialForms.Manifold.DeRham
