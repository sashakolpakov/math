import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ImmersionNormalForm
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter
import OAI.AlgebraicGeometry.CycleClass.Geometric.EmbeddedSupportComplement

/-! # Complex Normal Atlas -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalAtlas.Cycles

noncomputable section

/-!
# Actual normal neighborhoods of a closed complex immersion

The normal charts used here are supplied by the proved inverse-function
construction from an injective manifold differential. Their common normal
model has the difference of the two complex dimensions. The actual chart
neighborhoods together with the open complement of the full image cover the
ambient manifold.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]

/-- The codimension is the actual difference of complex model dimensions. -/
abbrev complexImmersionCodimension (E F : Type)
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] : ℕ :=
  Module.finrank ℂ F - Module.finrank ℂ E

/-- The normal form with a fixed complex coordinate space, derived from
the genuine differential and the inverse function theorem. -/
theorem complexImmersion_standardComplement (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x)) :
    Manifold.IsImmersionOfComplement (Fin (complexImmersionCodimension E F) → ℂ)
      𝓘(ℂ, E) 𝓘(ℂ, F) ω f :=
  ComplexPoints.Analytic.ImmersionComplementDimension.isImmersionOfComplement_of_forall_isImmersionAt
    (fun x => ComplexPoints.Analytic.ImmersionNormalForm.isImmersionAt_of_injective_mfderiv f x (hf x) (hi x))

variable (f : M → N)
  (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
  (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
  (he : Topology.IsClosedEmbedding f)

/-- An actual full-image normal pair at each source point. -/
def complexImmersionNormalPair (x : M) :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin (complexImmersionCodimension E F) → ℂ) f x :=
  ComplexPoints.Analytic.NormalPairRecenter.normalPairOfImmersion (complexImmersion_standardComplement f hf hi x)
    he.isEmbedding

/-- The corresponding genuine open ambient neighborhood. -/
def complexImmersionNormalOpen (x : M) : Opens N :=
  ⟨(complexImmersionNormalPair f hf hi he x).neighborhood,
    (complexImmersionNormalPair f hf hi he x).isOpen_neighborhood⟩

theorem complexImmersionNormalOpen_contains (x : M) :
    f x ∈ complexImmersionNormalOpen f hf hi he x :=
  (complexImmersionNormalPair f hf hi he x).point_mem_neighborhood

/-- The normal neighborhoods and the actual image complement cover every
ambient point; no cover is postulated as extra geometric data. -/
theorem complexImmersionNormalOpen_cover :
    iSup (complexImmersionNormalOpen f hf hi he) ⊔
      EmbeddedSupportComplement.Cycles.embeddedSupportComplement f he = ⊤ := by
  apply top_unique
  intro y _
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    exact Or.inl ((le_iSup (complexImmersionNormalOpen f hf hi he) x)
      (complexImmersionNormalOpen_contains f hf hi he x))
  · exact Or.inr hy

/-- In each actual open normal neighborhood, membership in the entire
closed image is equivalent to vanishing of the genuine normal coordinate. -/
theorem complexImmersionNormalPair_mem_range (x : M)
    (y : (complexImmersionNormalPair f hf hi he x).neighborhood) :
    y.val ∈ Set.range f ↔
      ((complexImmersionNormalPair f hf hi he x).homeomorph y).2.val = 0 :=
  (complexImmersionNormalPair f hf hi he x).mem_range_iff y

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalAtlas.Cycles
