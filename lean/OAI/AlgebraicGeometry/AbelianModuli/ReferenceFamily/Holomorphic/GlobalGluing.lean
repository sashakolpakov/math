import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LogClassComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Global Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing

noncomputable section

section

/-! Actual holomorphic changes of trivialization preserve the native
holomorphic unit-sheaf class. Together with Cech boundary detection,
this identifies cohomological equality with genuine holomorphic gauges. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

theorem holomorphicUnitSection_ext (V : Opens M)
    (s t : (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj.obj (.op V))
    (h : ∀ x : V, (LogUnitClass.holomorphicUnitSection E M V s).val x =
      (LogUnitClass.holomorphicUnitSection E M V t).val x) : s = t := by
  apply Units.ext
  exact ContMDiffMap.ext h

variable {I : Type} (U : I → Opens M)

theorem holomorphicUnitCech_gauge_boundary
    (k k' : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1)
    (g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U i))ˣ)
    (hg : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x =
        (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x *
          (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
            (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 0
      (DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
        (fun i => Additive.ofMul (g i))) = k' - k := by
  funext a
  apply holomorphicUnitSection_ext E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
  intro x
  have hd := DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections_delta (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
    (fun i => Additive.ofMul (g i)) a
  refine (congrArg (fun z => (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) z).val x) hd).trans ?_
  change (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (_ - _)).val x =
    (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a - k a)).val x
  rw [LogUnitClass.holomorphicUnitSection_value_sub, LogUnitClass.holomorphicUnitSection_value_sub]
  change (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
      (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩ =
    (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x /
      (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x
  rw [hg a x]
  have hne := DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero
    (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)) x
  field_simp

theorem holomorphicUnitCech_gauge_class
    (hU : ∀ x, ∃ i, x ∈ U i)
    (k k' : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1 k = 0)
    (hk' : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj U 1 k' = 0)
    (g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U i))ˣ)
    (hg : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k' a)).val x =
        (LogUnitClass.holomorphicUnitSection E M (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x *
          (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
            (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
        (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 k' hk' =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) U (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M)
        (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 k hk := by
  let F := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf E M
  let : AddCommGroup (CategoryTheory.Sheaf.H F 1) := Cech.Add.cechClassAddCommGroup F 1
  have hs := Cech.Add.cechSub_closed (X := TopCat.of M) U F.obj 1 k' k hk' hk
  have hz := DivisorClass.Chern.Cech.SheafBoundaries.abelianCechSheafClass_eq_zero_of_boundary (X := TopCat.of M) U F
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 (k' - k) hs
    (DivisorClass.Chern.Cech.LocalSections.abelianCechLocalSections (X := TopCat.of M) U F (fun i => Additive.ofMul (g i)))
    (holomorphicUnitCech_gauge_boundary E M U k k' g hg)
  have he := Cech.Add.cechSheafClass_sub (X := TopCat.of M) U F
    (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) 0 k' k hk' hk
  exact sub_eq_zero.mp (he.symm.trans hz)

theorem holomorphicLogUnitClass_gauge
    (hU : ∀ x, ∃ i, x ∈ U i) (l l' : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain (TopCat.of M) U)
    (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a))
    (hl' : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l' a))
    (h : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l)
    (h' : DivisorClass.Chern.LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l')
    (g : ∀ i, (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U i))ˣ)
    (hg : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a x) = Complex.exp (l a x) *
        (g (a 1)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property⟩ /
          (g (a 0)).val ⟨x.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩) :
    LogUnitClass.holomorphicLogUnitClass E M U l' hl' h' hU = LogUnitClass.holomorphicLogUnitClass E M U l hl h hU :=
  holomorphicUnitCech_gauge_class E M U hU (LogUnitClass.holomorphicLogUnitCech E M U l hl)
    (LogUnitClass.holomorphicLogUnitCech E M U l' hl') (LogUnitClass.holomorphicLogUnitCech_closed E M U l hl h)
    (LogUnitClass.holomorphicLogUnitCech_closed E M U l' hl' h') g hg

end

/-! Compatible holomorphic functions on a covering family of opens
glue to an actual holomorphic function on the original manifold. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries
open scoped _root_.Manifold ContDiff

theorem holomorphicFunction_global_glue
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] {I : Type}
    (U : I → Opens M) (hU : ∀ x, ∃ i, x ∈ U i)
    (f : ∀ i, DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U i))
    (hc : ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃ g : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M), ∀ i (x : U i), g x.val = f i x := by
  let F := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M
  have hcompat : TopCat.Presheaf.IsCompatible F.obj U f := by
    intro i j
    apply ContMDiffMap.ext
    intro x
    exact hc i j x.val x.property.1 x.property.2
  have hcover : (⊤ : Opens M) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr (hU x)
  obtain ⟨g, hg, _⟩ := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover f hcompat
  change DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := (⊤ : Opens M)) at g
  let t : M → (⊤ : Opens M) := fun x => ⟨x, by trivial⟩
  have ht : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ t :=
    (ContMDiff.subtypeVal_comp_iff (⊤ : Opens M) t).mp contMDiff_id
  refine ⟨⟨fun x => g (t x), g.property.comp ht⟩, ?_⟩
  intro i x
  exact congrArg (fun h : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U i) => h x) (hg i)

theorem holomorphicUnit_inverse_value
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    (u : (DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M))ˣ) (x : M) :
    (u⁻¹).val x = (u.val x)⁻¹ := by
  apply mul_left_cancel₀ (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero u x)
  exact (congrArg (fun h : DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := M) => h x) u.val_inv).trans
    (mul_inv_cancel₀ (DivisorClass.Chern.Holomorphic.SlitLog.holomorphicUnit_value_ne_zero u x)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing
