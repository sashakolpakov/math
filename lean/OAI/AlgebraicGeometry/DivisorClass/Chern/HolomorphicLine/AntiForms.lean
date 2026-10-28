import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Data
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothHolomorphicScalar

/-! # Anti Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms

noncomputable section

section

/-! Smooth forms with values in the actual holomorphic line bundle, defined by its original transition functions. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

abbrev holomorphicLineLocalSmoothForms (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (n : ℕ) :=
  ∀ i : M, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) n

def holomorphicLineSmoothFormSubmodule (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (n : ℕ) :
    Submodule ℂ (holomorphicLineLocalSmoothForms u U n) where
  carrier := {s | ∀ (i j x : M) (hx : x ∈ U)
    (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j),
      s j ⟨x, hx, hj⟩ = (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ • s i ⟨x, hx, hi⟩}
  zero_mem' := by
    intro i j x hx hi hj
    exact (smul_zero (A := TangentSpace 𝓘(ℝ, E) x [⋀^Fin n]→L[ℝ] ℂ)
      ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩)).symm
  add_mem' := by
    intro s t hs ht i j x hx hi hj
    change s j ⟨x, hx, hj⟩ + t j ⟨x, hx, hj⟩ = _ • (s i ⟨x, hx, hi⟩ + t i ⟨x, hx, hi⟩)
    rw [hs i j x hx hi hj, ht i j x hx hi hj, smul_add]
  smul_mem' := by
    intro z s hs i j x hx hi hj
    change z • s j ⟨x, hx, hj⟩ = _ • (z • s i ⟨x, hx, hi⟩)
    rw [hs i j x hx hi hj, smul_comm]

abbrev HolomorphicLineSmoothForm (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (n : ℕ) :=
  holomorphicLineSmoothFormSubmodule u U n

@[ext]
theorem holomorphicLineSmoothForm_ext {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U : Opens M} {n : ℕ}
    {s t : HolomorphicLineSmoothForm u U n}
    (h : ∀ (i : M) (x : ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)), s.val i x = t.val i x) : s = t := by
  apply Subtype.ext
  funext i
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext (h i)

def holomorphicLineSmoothFormRestrict {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V : Opens M} {n : ℕ}
    (h : V ≤ U) : HolomorphicLineSmoothForm u U n →ₗ[ℂ] HolomorphicLineSmoothForm u V n where
  toFun s := ⟨fun i => Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
    (inf_le_inf_right (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) h) (s.val i), by
      intro i j x hx hi hj
      exact s.property i j x (h hx) hi hj⟩
  map_add' s t := by
    apply holomorphicLineSmoothForm_ext
    intro i x
    rfl
  map_smul' z s := by
    apply holomorphicLineSmoothForm_ext
    intro i x
    rfl

theorem holomorphicLineSmoothFormRestrict_self {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U : Opens M} {n : ℕ}
    (s : HolomorphicLineSmoothForm u U n) : holomorphicLineSmoothFormRestrict le_rfl s = s := by
  apply holomorphicLineSmoothForm_ext
  intro i x
  rfl

theorem holomorphicLineSmoothFormRestrict_comp {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V W : Opens M} {n : ℕ}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : HolomorphicLineSmoothForm u U n) :
    holomorphicLineSmoothFormRestrict hWV (holomorphicLineSmoothFormRestrict hVU s) =
      holomorphicLineSmoothFormRestrict (hWV.trans hVU) s := by
  apply holomorphicLineSmoothForm_ext
  intro i x
  rfl

variable [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def holomorphicLineSectionSmoothZeroForm (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    HolomorphicSection.Data.HolomorphicLineSection u U →ₗ[ℂ] HolomorphicLineSmoothForm u U 0 where
  toFun s := ⟨fun i => Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (s.val i), by
    intro i j x hx hi hj
    ext v
    rw [ContinuousAlternatingMap.smul_apply, Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply, Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply]
    exact s.property i j x hx hi hj⟩
  map_add' s t := by
    apply holomorphicLineSmoothForm_ext
    intro i x
    ext v
    change Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (s.val i + t.val i) x v =
      Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (s.val i) x v + Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (t.val i) x v
    rw [Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply, Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply, Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply]
    rfl
  map_smul' z s := by
    apply holomorphicLineSmoothForm_ext
    intro i x
    ext v
    change Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (z • s.val i) x v = z • Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (s.val i) x v
    rw [Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply, Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply]
    rfl

theorem holomorphicLineSectionSmoothZeroForm_injective (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    Function.Injective (holomorphicLineSectionSmoothZeroForm u U) := by
  intro s t h
  apply HolomorphicSection.Data.holomorphicLineSection_ext
  intro i x
  have hx := congrArg (fun a : HolomorphicLineSmoothForm u U 0 => a.val i x 0) h
  change Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (s.val i) x 0 = Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm (t.val i) x 0 at hx
  rw [Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply, Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply] at hx
  exact hx

end

/-! Actual antiholomorphic forms with values in the original holomorphic line bundle. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def holomorphicLineAntiFormSubmodule (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (q : ℕ) :
    Submodule ℂ (HolomorphicLineSmoothForm u U q) where
  carrier := {a | ∀ i, a.val i ∈ Open.ManifoldBidegree.antiOpenManifoldFormSubmodule E (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) q}
  zero_mem' := fun i => (Open.ManifoldBidegree.antiOpenManifoldFormSubmodule E (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) q).zero_mem
  add_mem' := by
    intro a b ha hb i
    exact (Open.ManifoldBidegree.antiOpenManifoldFormSubmodule E _ q).add_mem (ha i) (hb i)
  smul_mem' := by
    intro z a ha i
    exact (Open.ManifoldBidegree.antiOpenManifoldFormSubmodule E _ q).smul_mem z (ha i)

abbrev HolomorphicLineAntiForm (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (q : ℕ) :=
  holomorphicLineAntiFormSubmodule u U q

instance holomorphicLineAntiForm_addCommGroup (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (q : ℕ) :
    AddCommGroup (HolomorphicLineAntiForm u U q) := Module.addCommMonoidToAddCommGroup ℂ

def holomorphicLineAntiFormRestrict {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V : Opens M} {q : ℕ}
    (h : V ≤ U) : HolomorphicLineAntiForm u U q →ₗ[ℂ] HolomorphicLineAntiForm u V q where
  toFun a := ⟨holomorphicLineSmoothFormRestrict h a.val, fun i =>
    Open.ManifoldBidegree.openManifoldHasBidegree_restrict (inf_le_inf_right (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) h) (a.property i)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem holomorphicLineAntiFormRestrict_self {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U : Opens M} {q : ℕ}
    (a : HolomorphicLineAntiForm u U q) : holomorphicLineAntiFormRestrict le_rfl a = a :=
  Subtype.ext (holomorphicLineSmoothFormRestrict_self a.val)

theorem holomorphicLineAntiFormRestrict_comp {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} {U V W : Opens M} {q : ℕ}
    (hVU : V ≤ U) (hWV : W ≤ V) (a : HolomorphicLineAntiForm u U q) :
    holomorphicLineAntiFormRestrict hWV (holomorphicLineAntiFormRestrict hVU a) =
      holomorphicLineAntiFormRestrict (hWV.trans hVU) a :=
  Subtype.ext (holomorphicLineSmoothFormRestrict_comp hVU hWV a.val)

def holomorphicLineAntiZeroEquiv (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) :
    HolomorphicLineSmoothForm u U 0 ≃ₗ[ℂ] HolomorphicLineAntiForm u U 0 where
  toFun a := ⟨a, fun _ _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
