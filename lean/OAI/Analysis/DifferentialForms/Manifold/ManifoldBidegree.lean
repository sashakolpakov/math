import OAI.Analysis.DifferentialForms.Manifold.Algebra
import OAI.Analysis.DifferentialForms.Manifold.Bidegree

/-! # Manifold Bidegree -/

namespace OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree

noncomputable section

/-! Genuine smooth manifold forms whose actual chart expressions have pure bidegree. -/

open scoped _root_.Manifold ContDiff
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {p q : ℕ}

variable (E M) in
/-- Pure bidegree of a tangent covector field, tested in the actual atlas.
Holomorphic transition invariance is proved in `ManifoldBidegreeInvariant`. -/
def HasManifoldBidegree (p q : ℕ) (form : Algebra.RawManifoldForm E M (p + q)) : Prop :=
  ∀ e ∈ atlas E M, ∀ y ∈ e.target, Bidegree.HasBidegree E p q (form.inChart e y)

namespace HasManifoldBidegree

theorem zero : HasManifoldBidegree E M p q (0 : Algebra.RawManifoldForm E M (p + q)) := by
  intro e _ y _
  rw [Algebra.RawManifoldForm.inChart_zero]
  exact (Bidegree.pureBidegreeSubmodule E p q).zero_mem

theorem add {form other : Algebra.RawManifoldForm E M (p + q)}
    (hform : HasManifoldBidegree E M p q form)
    (hother : HasManifoldBidegree E M p q other) :
    HasManifoldBidegree E M p q (form + other) := by
  intro e he y hy
  rw [Algebra.RawManifoldForm.inChart_add]
  exact (Bidegree.pureBidegreeSubmodule E p q).add_mem (hform e he y hy) (hother e he y hy)

theorem const_smul {form : Algebra.RawManifoldForm E M (p + q)}
    (hform : HasManifoldBidegree E M p q form) (c : ℂ) :
    HasManifoldBidegree E M p q (c • form) := by
  intro e he y hy
  rw [Algebra.RawManifoldForm.inChart_smul]
  exact (Bidegree.pureBidegreeSubmodule E p q).smul_mem c (hform e he y hy)

end HasManifoldBidegree

variable (E M) in
/-- The actual complex submodule of smooth manifold forms with pure chart values. -/
def pureManifoldFormSubmodule (p q : ℕ) : Submodule ℂ (Algebra.SmoothManifoldForm E M (p + q)) where
  carrier := {form | HasManifoldBidegree E M p q (form : Algebra.RawManifoldForm E M (p + q))}
  zero_mem' := HasManifoldBidegree.zero
  add_mem' := fun hform hother => hform.add hother
  smul_mem' := fun c _ hform => hform.const_smul c

@[simp]
theorem mem_pureManifoldFormSubmodule (form : Algebra.SmoothManifoldForm E M (p + q)) :
    form ∈ pureManifoldFormSubmodule E M p q ↔
      HasManifoldBidegree E M p q (form : Algebra.RawManifoldForm E M (p + q)) := Iff.rfl

variable (E M) in
/-- A smooth pure-type manifold form is an actual smooth covector field. -/
abbrev PureManifoldForm (p q : ℕ) := ↥(pureManifoldFormSubmodule E M p q)

namespace PureManifoldForm

instance : CoeFun (PureManifoldForm E M p q) (fun _ => Algebra.RawManifoldForm E M (p + q)) :=
  ⟨fun form => form.1⟩

theorem smooth (form : PureManifoldForm E M p q) :
    Algebra.IsSmoothManifoldFormOn (form : Algebra.RawManifoldForm E M (p + q)) univ := form.1.smooth

theorem hasManifoldBidegree (form : PureManifoldForm E M p q) :
    HasManifoldBidegree E M p q (form : Algebra.RawManifoldForm E M (p + q)) := form.2

theorem hasBidegree_inChart (form : PureManifoldForm E M p q)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    Bidegree.HasBidegree E p q ((form : Algebra.RawManifoldForm E M (p + q)).inChart e y) :=
  form.hasManifoldBidegree e he y hy

end PureManifoldForm

end

end OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree
