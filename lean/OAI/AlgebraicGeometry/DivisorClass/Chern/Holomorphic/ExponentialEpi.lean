import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SlitLog
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.AB

/-! # Exponential Epi -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ExponentialEpi

noncomputable section

section

/-! Local holomorphic logarithms prove that the actual exponential sheaf morphism is an epimorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

theorem holomorphicExponentialSheafMap_locallySurjective :
    TopCat.Presheaf.IsLocallySurjective (Holomorphic.Sheaves.holomorphicExponentialSheafMap E M).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  let u : (Exponential.HolomorphicFunction (E := E) (M := U))ˣ := Additive.toMul t
  let p : U := ⟨x, hx⟩
  let O := Exponential.holomorphicLogarithmOpen (u : Exponential.HolomorphicFunction (E := E) (M := U)) p
  let V : Opens M := U.isOpenEmbedding.functor.obj O
  have hVU : V ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact z.property
  have hxV : x ∈ V :=
    ⟨p, Exponential.mem_holomorphicLogarithmOpen (u : Exponential.HolomorphicFunction (E := E) (M := U)) p
      (SlitLog.holomorphicUnit_value_ne_zero u p), rfl⟩
  let g : Exponential.HolomorphicFunction (E := E) (M := V) :=
    ⟨fun y => (u : Exponential.HolomorphicFunction (E := E) (M := U)) (Opens.inclusion hVU y),
      u.val.property.comp (contMDiff_inclusion hVU)⟩
  have hs : ∀ y : V, g y / (u : Exponential.HolomorphicFunction (E := E) (M := U)) p ∈ Complex.slitPlane := by
    intro y
    have hy : Opens.inclusion hVU y ∈ O := by
      obtain ⟨z, hz, he⟩ := y.property
      exact (Subtype.ext he : z = Opens.inclusion hVU y) ▸ hz
    exact hy
  refine ⟨V, hVU, ⟨?_, hxV⟩⟩
  refine ⟨SlitLog.holomorphicSlitLog g ((u : Exponential.HolomorphicFunction (E := E) (M := U)) p) hs, ?_⟩
  apply Units.ext
  apply ContMDiffMap.ext
  intro y
  exact SlitLog.exp_holomorphicSlitLog g ((u : Exponential.HolomorphicFunction (E := E) (M := U)) p) hs
    (SlitLog.holomorphicUnit_value_ne_zero u p) y

theorem holomorphicExponentialSheafMap_epi : Epi (Holomorphic.Sheaves.holomorphicExponentialSheafMap E M) :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi (Holomorphic.Sheaves.holomorphicExponentialSheafMap E M)).mp
    (holomorphicExponentialSheafMap_locallySurjective E M)

end

/-! Actual logarithms on ambient subopens, extracted from the proved exponential sheaf epimorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem exists_holomorphicSubopenLog {U : Opens M}
    (g : (Exponential.HolomorphicFunction (E := E) (M := U))ˣ) (x : U) :
    ∃ (V : Opens M) (h : V ≤ U), x.val ∈ V ∧
      ∃ l : Exponential.HolomorphicFunction (E := E) (M := V),
        ∀ y : V, Complex.exp (l y) = g.val ⟨y.val, h y.property⟩ := by
  obtain ⟨V, hVU, ⟨l, hl⟩, hx⟩ :=
    ((TopCat.Presheaf.isLocallySurjective_iff (Holomorphic.Sheaves.holomorphicExponentialSheafMap E M).hom).mp
      (holomorphicExponentialSheafMap_locallySurjective E M))
      U (Additive.ofMul g) x.val x.property
  refine ⟨V, hVU, hx, l, ?_⟩
  intro y
  exact congrArg (fun t : Additive (Exponential.HolomorphicFunction (E := E) (M := V))ˣ =>
    (Additive.toMul t).val y) hl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ExponentialEpi
