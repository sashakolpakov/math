import OAI.Analysis.DifferentialForms.Manifold.Derivative
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Manifold De Rham -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
The de Rham complex of genuine smooth complex-valued forms on a smooth real
manifold. Its differential is the chart-independent exterior derivative already
constructed on actual tangent covectors. Its categorical cohomology is identified
with the quotient of closed forms by exact forms, including degree zero.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

universe u v

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type v) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual manifold exterior derivative has zero composite. -/
theorem Algebra.SmoothManifoldForm.d_comp_d (n : ℕ) :
    (Manifold.Algebra.SmoothManifoldForm.d :
      Manifold.Algebra.SmoothManifoldForm E M (n + 1) →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M (n + 1 + 1)).comp
      (Manifold.Algebra.SmoothManifoldForm.d :
        Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M (n + 1)) = 0 := by
  apply LinearMap.ext
  intro form
  exact Manifold.Algebra.SmoothManifoldForm.d_squared form

/-- The cochain complex of genuine global smooth manifold forms. -/
def ManifoldDeRham.manifoldDeRhamComplex : CochainComplex (ModuleCat.{max u v} ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (Manifold.Algebra.SmoothManifoldForm E M n))
    (fun _ => ModuleCat.ofHom Manifold.Algebra.SmoothManifoldForm.d)
    (fun n => ModuleCat.hom_ext (Manifold.Algebra.SmoothManifoldForm.d_comp_d E M n))

@[simp]
theorem ManifoldDeRham.manifoldDeRhamComplex_X (n : ℕ) :
    (ManifoldDeRham.manifoldDeRhamComplex E M).X n =
      ModuleCat.of ℂ (Manifold.Algebra.SmoothManifoldForm E M n) := rfl

@[simp]
theorem ManifoldDeRham.manifoldDeRhamComplex_d (n : ℕ) :
    (ManifoldDeRham.manifoldDeRhamComplex E M).d n (n + 1) = ModuleCat.ofHom
      (Manifold.Algebra.SmoothManifoldForm.d :
        Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M (n + 1)) := by
  exact CochainComplex.of_d
    (fun k => ModuleCat.of ℂ (Manifold.Algebra.SmoothManifoldForm E M k))
    (fun k => ModuleCat.ofHom (Manifold.Algebra.SmoothManifoldForm.d :
      Manifold.Algebra.SmoothManifoldForm E M k →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M (k + 1))) n

/-- The categorical differential is the constructed exterior derivative. -/
@[simp]
theorem ManifoldDeRham.manifoldDeRhamComplex_d_apply (n : ℕ) (form : Manifold.Algebra.SmoothManifoldForm E M n) :
    (ManifoldDeRham.manifoldDeRhamComplex E M).d n (n + 1) form = Manifold.Algebra.SmoothManifoldForm.d form := by
  rw [ManifoldDeRham.manifoldDeRhamComplex_d]
  rfl

/-- The complex de Rham cohomology of the smooth manifold. -/
def ManifoldDeRham.manifoldDeRhamCohomology (n : ℕ) : ModuleCat.{max u v} ℂ :=
  (ManifoldDeRham.manifoldDeRhamComplex E M).homology n

/-- The categorical cocycles of the genuine manifold de Rham complex. -/
def ManifoldDeRham.manifoldDeRhamCocycles (n : ℕ) : ModuleCat.{max u v} ℂ :=
  (ManifoldDeRham.manifoldDeRhamComplex E M).cycles n

/-- The canonical map from categorical cocycles to de Rham cohomology. -/
def ManifoldDeRham.manifoldDeRhamClass (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCocycles E M n ⟶ ManifoldDeRham.manifoldDeRhamCohomology E M n :=
  (ManifoldDeRham.manifoldDeRhamComplex E M).homologyπ n

/-- Categorical cocycles are the kernel of the outgoing exterior derivative. -/
def ManifoldDeRham.manifoldDeRhamCocyclesKernelIso (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCocycles E M n ≅
      ModuleCat.of ℂ (LinearMap.ker ((ManifoldDeRham.manifoldDeRhamComplex E M).sc n).g.hom) :=
  ((ManifoldDeRham.manifoldDeRhamComplex E M).sc n).moduleCatCyclesIso

/-- The standard module model of categorical de Rham cohomology. -/
def ManifoldDeRham.manifoldDeRhamCohomologyQuotientIso (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCohomology E M n ≅ ModuleCat.of ℂ
      (LinearMap.ker ((ManifoldDeRham.manifoldDeRhamComplex E M).sc n).g.hom ⧸
        LinearMap.range ((ManifoldDeRham.manifoldDeRhamComplex E M).sc n).moduleCatToCycles) :=
  ((ManifoldDeRham.manifoldDeRhamComplex E M).sc n).moduleCatHomologyIso

/-- Closed global smooth forms are precisely the kernel of exterior differentiation. -/
def ManifoldDeRham.manifoldClosedForms (n : ℕ) : Submodule ℂ (Manifold.Algebra.SmoothManifoldForm E M n) :=
  LinearMap.ker Manifold.Algebra.SmoothManifoldForm.d

instance ManifoldDeRham.manifoldClosedFormsAddCommGroup (n : ℕ) :
    AddCommGroup (ManifoldDeRham.manifoldClosedForms E M n) :=
  Submodule.addCommGroup (R := ℂ) (M := Manifold.Algebra.SmoothManifoldForm E M n)
    (ManifoldDeRham.manifoldClosedForms E M n)

@[simp]
theorem ManifoldDeRham.mem_manifoldClosedForms (n : ℕ) (form : Manifold.Algebra.SmoothManifoldForm E M n) :
    form ∈ ManifoldDeRham.manifoldClosedForms E M n ↔ Manifold.Algebra.SmoothManifoldForm.d form = 0 := Iff.rfl

/-- The incoming exterior derivative, with no incoming boundary in degree zero. -/
def ManifoldDeRham.manifoldIncomingExteriorDerivative :
    (n : ℕ) → Manifold.Algebra.SmoothManifoldForm E M (n - 1) →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M n
  | 0 => 0
  | _n + 1 => Manifold.Algebra.SmoothManifoldForm.d

@[simp]
theorem ManifoldDeRham.manifoldIncomingExteriorDerivative_zero :
    ManifoldDeRham.manifoldIncomingExteriorDerivative E M 0 = 0 := rfl

@[simp]
theorem ManifoldDeRham.manifoldIncomingExteriorDerivative_succ (n : ℕ) :
    ManifoldDeRham.manifoldIncomingExteriorDerivative E M (n + 1) = Manifold.Algebra.SmoothManifoldForm.d := rfl

theorem ManifoldDeRham.d_manifoldIncomingExteriorDerivative (n : ℕ)
    (form : Manifold.Algebra.SmoothManifoldForm E M (n - 1)) :
    Manifold.Algebra.SmoothManifoldForm.d (ManifoldDeRham.manifoldIncomingExteriorDerivative E M n form) = 0 := by
  cases n with
  | zero => simp
  | succ n => exact Manifold.Algebra.SmoothManifoldForm.d_squared form

/-- Exact global smooth forms are the image of the incoming exterior derivative. -/
def ManifoldDeRham.manifoldExactForms (n : ℕ) : Submodule ℂ (Manifold.Algebra.SmoothManifoldForm E M n) :=
  LinearMap.range (ManifoldDeRham.manifoldIncomingExteriorDerivative E M n)

@[simp]
theorem ManifoldDeRham.manifoldExactForms_zero : ManifoldDeRham.manifoldExactForms E M 0 = ⊥ := by
  simp [ManifoldDeRham.manifoldExactForms]

@[simp]
theorem ManifoldDeRham.manifoldExactForms_succ (n : ℕ) :
    ManifoldDeRham.manifoldExactForms E M (n + 1) = LinearMap.range
      (Manifold.Algebra.SmoothManifoldForm.d :
        Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M (n + 1)) := rfl

theorem ManifoldDeRham.manifoldExactForms_le_closedForms (n : ℕ) :
    ManifoldDeRham.manifoldExactForms E M n ≤ ManifoldDeRham.manifoldClosedForms E M n := by
  rintro form ⟨primitive, rfl⟩
  exact ManifoldDeRham.d_manifoldIncomingExteriorDerivative E M n primitive

/-- The incoming derivative with codomain restricted to closed forms. -/
def ManifoldDeRham.manifoldBoundaryToClosed (n : ℕ) :
    Manifold.Algebra.SmoothManifoldForm E M (n - 1) →ₗ[ℂ] ManifoldDeRham.manifoldClosedForms E M n :=
  (ManifoldDeRham.manifoldIncomingExteriorDerivative E M n).codRestrict (ManifoldDeRham.manifoldClosedForms E M n)
    (ManifoldDeRham.d_manifoldIncomingExteriorDerivative E M n)

@[simp]
theorem ManifoldDeRham.manifoldBoundaryToClosed_coe (n : ℕ) (form : Manifold.Algebra.SmoothManifoldForm E M (n - 1)) :
    (ManifoldDeRham.manifoldBoundaryToClosed E M n form : Manifold.Algebra.SmoothManifoldForm E M n) =
      ManifoldDeRham.manifoldIncomingExteriorDerivative E M n form := rfl

/-- Exact forms as a submodule of closed forms. -/
def ManifoldDeRham.manifoldExactClosedForms (n : ℕ) : Submodule ℂ (ManifoldDeRham.manifoldClosedForms E M n) :=
  LinearMap.range (ManifoldDeRham.manifoldBoundaryToClosed E M n)

theorem ManifoldDeRham.mem_manifoldExactClosedForms_iff (n : ℕ) (form : ManifoldDeRham.manifoldClosedForms E M n) :
    form ∈ ManifoldDeRham.manifoldExactClosedForms E M n ↔
      ∃ primitive : Manifold.Algebra.SmoothManifoldForm E M (n - 1),
        ManifoldDeRham.manifoldIncomingExteriorDerivative E M n primitive = form.val := by
  constructor
  · rintro ⟨primitive, rfl⟩
    exact ⟨primitive, rfl⟩
  · rintro ⟨primitive, hprimitive⟩
    exact ⟨primitive, Subtype.ext hprimitive⟩

/-- The literal quotient of closed global smooth forms by exact forms. -/
abbrev ManifoldDeRham.manifoldDeRhamFormQuotient (n : ℕ) :=
  ManifoldDeRham.manifoldClosedForms E M n ⧸ ManifoldDeRham.manifoldExactClosedForms E M n

/-- The explicit short complex of global exterior derivatives around degree `n`. -/
def ManifoldDeRham.manifoldFormShortComplex (n : ℕ) : ShortComplex (ModuleCat.{max u v} ℂ) where
  X₁ := ModuleCat.of ℂ (Manifold.Algebra.SmoothManifoldForm E M (n - 1))
  X₂ := ModuleCat.of ℂ (Manifold.Algebra.SmoothManifoldForm E M n)
  X₃ := ModuleCat.of ℂ (Manifold.Algebra.SmoothManifoldForm E M (n + 1))
  f := ModuleCat.ofHom (ManifoldDeRham.manifoldIncomingExteriorDerivative E M n)
  g := ModuleCat.ofHom (Manifold.Algebra.SmoothManifoldForm.d :
    Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M (n + 1))
  zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact ManifoldDeRham.d_manifoldIncomingExteriorDerivative E M n form

theorem ManifoldDeRham.manifoldDeRhamComplex_incoming (n : ℕ) :
    (ManifoldDeRham.manifoldDeRhamComplex E M).d (n - 1) n =
      ModuleCat.ofHom (ManifoldDeRham.manifoldIncomingExteriorDerivative E M n) := by
  cases n with
  | zero =>
      change (ManifoldDeRham.manifoldDeRhamComplex E M).d 0 0 = 0
      exact (ManifoldDeRham.manifoldDeRhamComplex E M).shape 0 0 (by simp [ComplexShape.up_Rel])
  | succ n => simpa only [Nat.succ_sub_one, ManifoldDeRham.manifoldIncomingExteriorDerivative_succ] using
      ManifoldDeRham.manifoldDeRhamComplex_d E M n

/-- The canonical short complex is the explicit exterior-derivative short complex. -/
def ManifoldDeRham.manifoldDeRhamFormShortComplexIso (n : ℕ) :
    (ManifoldDeRham.manifoldDeRhamComplex E M).sc n ≅ ManifoldDeRham.manifoldFormShortComplex E M n :=
  (ManifoldDeRham.manifoldDeRhamComplex E M).isoSc' (n - 1) n (n + 1)
      (by cases n <;> simp) (CochainComplex.next ℕ n) ≪≫
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change ModuleCat.ofHom (ManifoldDeRham.manifoldIncomingExteriorDerivative E M n) =
          (ManifoldDeRham.manifoldDeRhamComplex E M).d (n - 1) n
        exact (ManifoldDeRham.manifoldDeRhamComplex_incoming E M n).symm)
      (by
        change ModuleCat.ofHom (Manifold.Algebra.SmoothManifoldForm.d :
          Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M (n + 1)) =
            (ManifoldDeRham.manifoldDeRhamComplex E M).d n (n + 1)
        exact (ManifoldDeRham.manifoldDeRhamComplex_d E M n).symm)

/-- Categorical de Rham cohomology is precisely closed forms modulo exact forms. -/
def ManifoldDeRham.manifoldDeRhamFormQuotientIso (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCohomology E M n ≅ ModuleCat.of ℂ (ManifoldDeRham.manifoldDeRhamFormQuotient E M n) :=
  ShortComplex.homologyMapIso (ManifoldDeRham.manifoldDeRhamFormShortComplexIso E M n) ≪≫
    (ManifoldDeRham.manifoldFormShortComplex E M n).moduleCatHomologyIso

/-- The cohomology class of a genuine closed global smooth form. -/
def ManifoldDeRham.manifoldDeRhamFormClass (n : ℕ) :
    ManifoldDeRham.manifoldClosedForms E M n →ₗ[ℂ] ManifoldDeRham.manifoldDeRhamCohomology E M n :=
  (ManifoldDeRham.manifoldDeRhamFormQuotientIso E M n).toLinearEquiv.symm.toLinearMap.comp
    (ManifoldDeRham.manifoldExactClosedForms E M n).mkQ

/-- A closed global smooth form represents zero exactly when it is exact. -/
theorem ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (n : ℕ) (form : ManifoldDeRham.manifoldClosedForms E M n) :
    ManifoldDeRham.manifoldDeRhamFormClass E M n form = 0 ↔
      ∃ primitive : Manifold.Algebra.SmoothManifoldForm E M (n - 1),
        ManifoldDeRham.manifoldIncomingExteriorDerivative E M n primitive = form.val := by
  change (ManifoldDeRham.manifoldDeRhamFormQuotientIso E M n).toLinearEquiv.symm
      ((ManifoldDeRham.manifoldExactClosedForms E M n).mkQ form) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ManifoldDeRham.mem_manifoldExactClosedForms_iff E M n form

end

end OAI.Analysis.DifferentialForms.Manifold
