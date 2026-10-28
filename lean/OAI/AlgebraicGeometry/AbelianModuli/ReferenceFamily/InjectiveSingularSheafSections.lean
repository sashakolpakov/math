import OAI.AlgebraicTopology.Cohomology.Singular.ParacompactComparison

/-! # Injective Singular Sheaf Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InjectiveSingularSheafSections.InjectiveSingularComparison

noncomputable section

/-! Actual singular-to-sheafified-section comparison for injective integral
coefficient modules, including rational-mod-integral coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicTopology.Cohomology.Singular.ParacompactComparison

/-- A locally zero positive-degree cocycle has a locally zero primitive.
The primitive vanishes on the same chosen open cover's small simplices. -/
theorem exists_locallyZeroSingularPrimitive (M : ModuleCat.{0} ℤ) [Injective M]
    (X : TopCat.{0}) (n : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X (n + 1))
    (hc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d (n + 1) (n + 2) c = 0)
    (hlocal : AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.IsLocallyZeroSingularCochain M X (n + 1) c) :
    ∃ b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n,
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d n (n + 1) b = c ∧
        AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.IsLocallyZeroSingularCochain M X n b := by
  obtain ⟨U, hU, hsmall⟩ :=
    (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.isLocallyZeroSingularCochain_iff_smallRestriction M X (n + 1) c).1 hlocal
  have : QuasiIso (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun x => (U x : Set X))) :=
    AlgebraicTopology.Cohomology.Singular.SmallCochainComparison.smallSingularRestriction_quasiIso_int X (fun x => (U x : Set X)) M
      (fun x => (U x).isOpen) (fun x => ⟨x, hU x⟩)
  obtain ⟨b, hb, hbsmall⟩ := AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso.exists_primitive_in_kernel_of_surjective_quasiIso
    (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun x => (U x : Set X)))
    (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.smallSingularRestriction_f_surjective M X (fun x => (U x : Set X)))
    n c hc hsmall
  exact ⟨b, hb,
    (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.isLocallyZeroSingularCochain_iff_smallRestriction M X n b).2
      ⟨U, hU, hbsmall⟩⟩

/-- A locally zero closed singular zero-cochain vanishes. -/
theorem locallyZeroSingularCocycle_zero (M : ModuleCat.{0} ℤ) [Injective M]
    (X : TopCat.{0}) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X 0)
    (hc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 c = 0)
    (hlocal : AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.IsLocallyZeroSingularCochain M X 0 c) : c = 0 := by
  obtain ⟨U, hU, hsmall⟩ :=
    (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.isLocallyZeroSingularCochain_iff_smallRestriction M X 0 c).1 hlocal
  have : QuasiIso (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun x => (U x : Set X))) :=
    AlgebraicTopology.Cohomology.Singular.SmallCochainComparison.smallSingularRestriction_quasiIso_int X (fun x => (U x : Set X)) M
      (fun x => (U x).isOpen) (fun x => ⟨x, hU x⟩)
  exact AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso.cochain_eq_zero_in_kernel_of_surjective_quasiIso
    (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun x => (U x : Set X)))
    (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.smallSingularRestriction_f_surjective M X (fun x => (U x : Set X)))
    c hc hsmall

/-- The genuine locally zero singular subcomplex is acyclic for injective integral coefficients. This requires no local or global hypothesis on X. -/
theorem locallyZeroSingularCochains_acyclic (M : ModuleCat.{0} ℤ) [Injective M]
    (X : TopCat.{0}) : (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.locallyZeroSingularCochains M X).Acyclic := by
  let K := AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.locallyZeroSingularCochains M X
  let i := AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.locallyZeroSingularInclusion M X
  intro k
  cases k with
  | zero =>
    apply (K.exactAt_iff' 0 0 1 (by simp) (by simp)).2
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    have hc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 0 1 (i.f 0 z) = 0 := by
      simpa only [map_zero] using AlgebraicTopology.Cohomology.Singular.LocalPrimitives.cochainMap_primitive i 0 z 0 hz
    have hz0 := locallyZeroSingularCocycle_zero M X (i.f 0 z) hc
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.locallyZeroSingularInclusion_isLocallyZero M X 0 z)
    have hzero : z = 0 := by
      apply AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.locallyZeroSingularInclusion_f_injective M X 0
      change i.f 0 z = i.f 0 0
      rw [hz0, map_zero]
    refine ⟨0, ?_⟩
    change K.d 0 0 0 = z
    exact (K.d 0 0).hom.map_zero.trans hzero.symm
  | succ n =>
    apply (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).2
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    have hc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d (n + 1) (n + 2)
        (i.f (n + 1) z) = 0 := by
      simpa only [map_zero] using AlgebraicTopology.Cohomology.Singular.LocalPrimitives.cochainMap_primitive i (n + 1) z 0 hz
    obtain ⟨b, hb, hblocal⟩ := exists_locallyZeroSingularPrimitive M X n (i.f (n + 1) z) hc
      (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.locallyZeroSingularInclusion_isLocallyZero M X (n + 1) z)
    obtain ⟨w, hw⟩ := AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.exists_locallyZeroSingularLift M X n b hblocal
    refine ⟨w, ?_⟩
    apply AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.locallyZeroSingularInclusion_f_injective M X (n + 1)
    change i.f (n + 1) (K.d n (n + 1) w) = i.f (n + 1) z
    have hcomm := AlgebraicTopology.Cohomology.Singular.LocalPrimitives.cochainMap_primitive i n w (K.d n (n + 1) w) rfl
    exact hcomm.symm.trans ((congrArg ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d n (n + 1)) hw).trans hb)

theorem quasiIso_singularCochainsToSheafSections (M : ModuleCat.{0} ℤ) [Injective M]
    (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] :
    QuasiIso (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X) :=
  AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso.quasiIso_of_surjective_of_acyclic_kernel (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X)
    (AlgebraicTopology.Cohomology.Singular.ParacompactComparison.singularCochainsToSheafSections_surjective_of_paracompact M X)
    (locallyZeroSingularCochains_acyclic M X)

def singularSheafSectionsIso (M : ModuleCat.{0} ℤ) [Injective M]
    (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X n ≅ (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections M X).homology n := by
  have := quasiIso_singularCochainsToSheafSections M X
  exact isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections M X) n

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InjectiveSingularSheafSections.InjectiveSingularComparison
