import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Cube Neighborhood Extension -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CubeNeighborhoodExtension

noncomputable section

/-!
# Smooth compression into a neighborhood of the unit cube

Every open neighborhood of the actual closed unit cube contains the image
of a globally smooth parameter map that equals the identity near that cube.
The map is formed in the vector parameter space using a smooth scalar
cutoff supported in a small convex thickening of the cube.

Composition then extends maps to arbitrary target manifolds. The target
manifold itself is never subjected to vector addition or scalar averaging.
-/

open Filter Set _root_.TopologicalSpace Function OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped _root_.Topology ContDiff _root_.Manifold

/-- A globally smooth parameter compression into any open neighborhood of
the closed unit cube, with identity germ along the entire cube. -/
theorem exists_contDiff_cube_compression {n : ℕ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hKU : StokesF.SingularCubeStokes.unitCube n ⊆ U) :
    ∃ g : (Fin n → ℝ) → (Fin n → ℝ), ContDiff ℝ ∞ g ∧ range g ⊆ U ∧
      g =ᶠ[𝓝ˢ (StokesF.SingularCubeStokes.unitCube n)] id := by
  have hK : IsCompact (StokesF.SingularCubeStokes.unitCube n) := isCompact_Icc
  have hconv : Convex ℝ (StokesF.SingularCubeStokes.unitCube n) := convex_Icc _ _
  have hzero : (0 : Fin n → ℝ) ∈ StokesF.SingularCubeStokes.unitCube n := by
    constructor
    · exact le_rfl
    · intro i
      exact zero_le_one
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  let V : Set (Fin n → ℝ) := Metric.thickening δ (StokesF.SingularCubeStokes.unitCube n)
  have hV : IsOpen V := Metric.isOpen_thickening
  have hKV : StokesF.SingularCubeStokes.unitCube n ⊆ V := Metric.self_subset_thickening hδ _
  have hVconv : Convex ℝ V := hconv.thickening δ
  have h0V : (0 : Fin n → ℝ) ∈ V := hKV hzero
  obtain ⟨rho, hone, hzeroOutside, hrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, Fin n → ℝ))
      (s := StokesF.SingularCubeStokes.unitCube n) (t := V)
      hK.isClosed (by simpa only [hV.interior_eq] using hKV) (n := ⊤)
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => rho x • x
  refine ⟨g, ?_, ?_, ?_⟩
  · exact rho.contMDiff.contDiff.smul contDiff_id
  · rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ V
    · apply hδU
      have hcomb := hVconv hx h0V (hrange x).1
        (sub_nonneg.mpr (hrange x).2) (by ring : rho x + (1 - rho x) = 1)
      simpa only [smul_zero, add_zero] using hcomb
    · have hrho : rho x = 0 := hzeroOutside x hx
      simpa only [g, hrho, zero_smul] using hKU hzero
  · filter_upwards [hone] with x hx
    change rho x • x = x
    rw [hx, one_smul]

/-- The compression is also an actual smooth map into the open subtype,
equipped with its inherited manifold structure. -/
theorem exists_contMDiff_cube_compression {n : ℕ} (U : Opens (Fin n → ℝ))
    (hKU : StokesF.SingularCubeStokes.unitCube n ⊆ U) :
    ∃ g : (Fin n → ℝ) → U,
      ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, Fin n → ℝ)) ∞ g ∧
      (Subtype.val ∘ g) =ᶠ[𝓝ˢ (StokesF.SingularCubeStokes.unitCube n)] id := by
  obtain ⟨g, hg, hgu, hid⟩ := exists_contDiff_cube_compression U.isOpen hKU
  let r : (Fin n → ℝ) → U := fun x => ⟨g x, hgu ⟨x, rfl⟩⟩
  refine ⟨r, ?_, hid⟩
  apply (ContMDiff.subtypeVal_comp_iff U r).mp
  exact hg.contMDiff

/-- A smooth map on a neighborhood of the cube, with values in any target
manifold, has a globally smooth cube representative agreeing near the cube.
The witness of domain membership in the agreement statement ensures that
the equality compares the actual locally defined map. -/
theorem exists_global_contMDiff_of_cube_neighborhood
    {n : ℕ} {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ F H) (U : Opens (Fin n → ℝ))
    (hKU : StokesF.SingularCubeStokes.unitCube n ⊆ U) {f : U → M}
    (hf : ContMDiff (𝓘(ℝ, Fin n → ℝ)) I ∞ f) :
    ∃ g : (Fin n → ℝ) → M, ContMDiff (𝓘(ℝ, Fin n → ℝ)) I ∞ g ∧
      ∀ᶠ x in 𝓝ˢ (StokesF.SingularCubeStokes.unitCube n), ∃ hx : x ∈ U, g x = f ⟨x, hx⟩ := by
  obtain ⟨r, hr, hid⟩ := exists_contMDiff_cube_compression U hKU
  refine ⟨f ∘ r, hf.comp hr, ?_⟩
  filter_upwards [hid] with x hx
  change (r x).val = x at hx
  have hxU : x ∈ U := hx ▸ (r x).property
  refine ⟨hxU, ?_⟩
  exact congrArg f (Subtype.ext hx)

end

end OAI.AlgebraicTopology.DeRham.Comparison.CubeNeighborhoodExtension
