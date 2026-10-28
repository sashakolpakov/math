import OAI.AlgebraicGeometry.DivisorClass.Chern.Logarithms
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Exponential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential

noncomputable section

section

/-! Actual holomorphic local logarithms for the analytic exponential sequence. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

abbrev HolomorphicFunction := C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯

def holomorphicLogarithmOpen (g : HolomorphicFunction (E := E) (M := M)) (p : M) : Opens M :=
  ⟨Logarithms.Construction.logarithmNeighborhood (⟨g.val, g.property.continuous⟩ : C(M, ℂ)) p,
    Logarithms.Construction.isOpen_logarithmNeighborhood (⟨g.val, g.property.continuous⟩ : C(M, ℂ)) p⟩

theorem mem_holomorphicLogarithmOpen (g : HolomorphicFunction (E := E) (M := M))
    (p : M) (hp : g p ≠ 0) : p ∈ holomorphicLogarithmOpen g p :=
  Logarithms.Construction.mem_logarithmNeighborhood (⟨g.val, g.property.continuous⟩ : C(M, ℂ)) p hp

def holomorphicLocalLogarithm (g : HolomorphicFunction (E := E) (M := M)) (p : M) :
    C^∞⟮𝓘(ℂ, E), holomorphicLogarithmOpen g p; 𝓘(ℂ), ℂ⟯ where
  val q := Complex.log (g q / g p) + Complex.log (g p)
  property := by
    have hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞
        (fun q : holomorphicLogarithmOpen g p => g q) :=
      g.property.comp contMDiff_subtype_val
    intro q
    have hq : g q / g p ∈ Complex.slitPlane := q.property
    have hr : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ∞
        (fun r : holomorphicLogarithmOpen g p => g r / g p) q := by
      simpa only [div_eq_mul_inv] using! (hg.mul contMDiff_const).contMDiffAt
    exact ((Complex.contDiffAt_log hq).contMDiffAt.comp q hr).add contMDiffAt_const

theorem exp_holomorphicLocalLogarithm (g : HolomorphicFunction (E := E) (M := M))
    (p : M) (hp : g p ≠ 0) (q : holomorphicLogarithmOpen g p) :
    Complex.exp (holomorphicLocalLogarithm g p q) = g q :=
  Logarithms.Construction.exp_localLogarithm (⟨g.val, g.property.continuous⟩ : C(M, ℂ)) p hp q

theorem exists_local_holomorphic_logarithm (g : HolomorphicFunction (E := E) (M := M))
    (p : M) (hp : g p ≠ 0) :
    ∃ (U : Opens M), p ∈ U ∧ ∃ l : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯,
      ∀ q : U, Complex.exp (l q) = g q :=
  ⟨holomorphicLogarithmOpen g p, mem_holomorphicLogarithmOpen g p hp,
    holomorphicLocalLogarithm g p, exp_holomorphicLocalLogarithm g p hp⟩

end

/-! The actual holomorphic exponential and its exact integral-period kernel. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicExpFunction (g : HolomorphicFunction (E := E) (M := M)) :
    HolomorphicFunction (E := E) (M := M) :=
  ⟨fun x => Complex.exp (g x), Complex.contDiff_exp.contMDiff.comp g.property⟩

def holomorphicExpUnit (g : HolomorphicFunction (E := E) (M := M)) :
    (HolomorphicFunction (E := E) (M := M))ˣ where
  val := holomorphicExpFunction g
  inv := holomorphicExpFunction (-g)
  val_inv := by
    apply ContMDiffMap.ext
    intro x
    change Complex.exp (g x) * Complex.exp (-g x) = 1
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by
    apply ContMDiffMap.ext
    intro x
    change Complex.exp (-g x) * Complex.exp (g x) = 1
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

theorem holomorphicExpUnit_zero : holomorphicExpUnit (0 : HolomorphicFunction (E := E) (M := M)) = 1 := by
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_zero

theorem holomorphicExpUnit_add (g h : HolomorphicFunction (E := E) (M := M)) :
    holomorphicExpUnit (g+h) = holomorphicExpUnit g * holomorphicExpUnit h := by
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_add (g x) (h x)

def holomorphicExponential : HolomorphicFunction (E := E) (M := M) →+
    Additive (HolomorphicFunction (E := E) (M := M))ˣ where
  toFun g := Additive.ofMul (holomorphicExpUnit g)
  map_zero' := holomorphicExpUnit_zero
  map_add' := holomorphicExpUnit_add

def holomorphicPeriodFunction (n : LocallyConstant M ℤ) : HolomorphicFunction (E := E) (M := M) where
  val x := (n x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  property := by
    intro x
    apply (contMDiffAt_const (c := (n x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))).congr_of_eventuallyEq
    filter_upwards [n.isLocallyConstant.eventually_eq x] with y hy
    change n y = n x at hy
    rw [hy]

theorem holomorphicPeriodFunction_injective : Function.Injective (holomorphicPeriodFunction (E := E) (M := M)) := by
  intro n m h
  apply LocallyConstant.ext
  intro x
  have hx := congrArg (fun f : HolomorphicFunction (E := E) (M := M) => f x) h
  change (n x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
    (m x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) at hx
  exact_mod_cast (mul_right_cancel₀ Complex.two_pi_I_ne_zero hx)

theorem exp_holomorphicPeriodFunction (n : LocallyConstant M ℤ) :
    holomorphicExpUnit (holomorphicPeriodFunction (E := E) n) = 1 := by
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  exact Complex.exp_eq_one_iff.mpr ⟨n x, rfl⟩

def holomorphicKernelInteger (g : HolomorphicFunction (E := E) (M := M))
    (h : ∀ x, Complex.exp (g x) = 1) : LocallyConstant M ℤ :=
  ⟨fun x => Logarithms.Construction.logarithmicDefect (g x) 0 0 (by simpa only [Complex.exp_zero, mul_one] using h x),
    Logarithms.Construction.isLocallyConstant_logarithmicDefect (⟨g.val, g.property.continuous⟩ : C(M, ℂ)) 0 0
      (fun x => by simpa only [ContinuousMap.zero_apply, Complex.exp_zero, mul_one] using! h x)⟩

theorem holomorphicKernelInteger_spec (g : HolomorphicFunction (E := E) (M := M))
    (h : ∀ x, Complex.exp (g x) = 1) :
    holomorphicPeriodFunction (E := E) (holomorphicKernelInteger g h) = g := by
  apply ContMDiffMap.ext
  intro x
  have hs := Logarithms.Construction.logarithmicDefect_spec (g x) 0 0
    (by simpa only [Complex.exp_zero, mul_one] using h x)
  simpa only [add_zero, sub_zero] using! hs.symm

theorem holomorphicExponential_kernel (g : HolomorphicFunction (E := E) (M := M)) :
    holomorphicExpUnit g = 1 ↔ ∃ n : LocallyConstant M ℤ, holomorphicPeriodFunction (E := E) n = g := by
  constructor
  · intro h
    have hp : ∀ x, Complex.exp (g x) = 1 := fun x =>
      congrArg (fun u : (HolomorphicFunction (E := E) (M := M))ˣ => (u : HolomorphicFunction (E := E) (M := M)) x) h
    exact ⟨holomorphicKernelInteger g hp, holomorphicKernelInteger_spec g hp⟩
  · rintro ⟨n, rfl⟩
    exact exp_holomorphicPeriodFunction n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential
