import OAI.AlgebraicTopology.Kunneth.ManifoldWedge
import OAI.AlgebraicTopology.Kunneth.WedgeAlgebra
import OAI.Analysis.DifferentialForms.Manifold.OpenDerivative

/-! # Manifold Wedge -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge

noncomputable section

/-! The original exterior product on actual ambient open manifold forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {U W : Opens M} {p q : ℕ}

local instance openWedge_tangentNormedGroup (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance openWedge_tangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

def openManifoldWedge (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (p + q) :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw U (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge a.extension b.extension)
    (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.isSmoothManifoldFormOn_wedge a.smooth b.smooth)

theorem openManifoldWedge_apply (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) (x : U) :
    openManifoldWedge a b x = AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a x) (b x) := by
  change AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a.extension x.val) (b.extension x.val) = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply a x, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply b x]

theorem openManifoldWedge_restrict (h : W ≤ U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openManifoldWedge a b) =
      openManifoldWedge (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h b) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply, openManifoldWedge_apply, openManifoldWedge_apply]
  rfl

theorem openManifoldWedge_inChart (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q)
    (e : OpenPartialHomeomorph M E) {y : E} (hy : e.symm y ∈ U) :
    (openManifoldWedge a b).extension.inChart e y =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a.extension.inChart e y) (b.extension.inChart e y) := by
  unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩, openManifoldWedge_apply,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply a ⟨e.symm y, hy⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply b ⟨e.symm y, hy⟩]
  exact (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback _ _ _).symm

theorem openManifoldWedge_add_left (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    openManifoldWedge (a + b) c = openManifoldWedge a c + openManifoldWedge b c := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [openManifoldWedge_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_add_left]

theorem openManifoldWedge_add_right (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    openManifoldWedge a (b + c) = openManifoldWedge a b + openManifoldWedge a c := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [openManifoldWedge_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_add_right]

theorem openManifoldWedge_smul_left (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    openManifoldWedge (c • a) b = c • openManifoldWedge a b := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [openManifoldWedge_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smul_apply, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_left]

theorem openManifoldWedge_smul_right (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    openManifoldWedge a (c • b) = c • openManifoldWedge a b := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [openManifoldWedge_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smul_apply, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_right]

def openManifoldWedgeRight (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (p + q) where
  toFun := openManifoldWedge a
  map_add' := openManifoldWedge_add_right a
  map_smul' c b := openManifoldWedge_smul_right c a b

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldWedge
