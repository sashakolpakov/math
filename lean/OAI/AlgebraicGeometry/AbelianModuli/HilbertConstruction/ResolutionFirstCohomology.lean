import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicSheafResolution

/-! # Resolution First Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionFirstCohomology.IntrinsicCech

noncomputable section

/-! The first potentially nonzero cohomology of a resolved sheaf embeds into the kernel of the first differential on the cohomology of its resolution terms. This uses only a bounded range of termwise vanishing. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite
universe u

variable {X : TopCat.{u}}

theorem sheafCohomology_map_zero_injective
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (a : F ⟶ G) [Mono a] :
    Function.Injective (CategoryTheory.Sheaf.H.map a 0) := by
  let T := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)
  let : T.IsRightAdjoint :=
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).isRightAdjoint
  have : Mono (T.map a) := inferInstance
  have hi : Function.Injective (a.hom.app (op ⊤)) :=
    (AddCommGrpCat.mono_iff_injective (T.map a)).mp inferInstance
  intro x y hxy
  apply (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).injective
  apply hi
  rw [CategoryTheory.Sheaf.H.equiv₀_naturality, CategoryTheory.Sheaf.H.equiv₀_naturality, hxy]

theorem sheafCohomology_zero_vanish_of_mono
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (a : F ⟶ G) [Mono a]
    (hG : Subsingleton (CategoryTheory.Sheaf.H G 0)) :
    Subsingleton (CategoryTheory.Sheaf.H F 0) := by
  let : Subsingleton (CategoryTheory.Sheaf.H G 0) := hG
  refine subsingleton_of_forall_eq 0 fun x => ?_
  exact sheafCohomology_map_zero_injective a (Subsingleton.elim _ _)

theorem sheafCohomology_map_succ_injective_of_shortExact
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    (hZ : Subsingleton (CategoryTheory.Sheaf.H S.X₃ n)) :
    Function.Injective (CategoryTheory.Sheaf.H.map S.f (n + 1)) := by
  let : Subsingleton (CategoryTheory.Sheaf.H S.X₃ n) := hZ
  intro x y hxy
  have hz : CategoryTheory.Sheaf.H.map S.f (n + 1) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, h⟩ := HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₁_explicit hS n (n + 1) rfl (x - y) hz
  rw [Subsingleton.elim z 0, map_zero] at h
  exact sub_eq_zero.mp h.symm

variable (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ)

theorem resolutionCycles_cohomology_vanish_below
    (hpos : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (q : ℕ) (hK : ∀ p r, r < q → Subsingleton (CategoryTheory.Sheaf.H (K.X p) r))
    (n r : ℕ) (hr : r < q) :
    Subsingleton (CategoryTheory.Sheaf.H (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).cycles r) := by
  induction r generalizing n with
  | zero =>
    exact sheafCohomology_zero_vanish_of_mono
      (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).iCycles (hK (n + 1) 0 hr)
  | succ r ih =>
    apply HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.subsingleton_H_X₁_succ_of_shortExact
      (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hpos n) r
    · exact ih (n + 1) (by omega)
    · exact hK (n + 1) (r + 1) hr

theorem resolution_firstCohomology_injective
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (e : F ⟶ K.X 0) [Mono e] (w : e ≫ K.d 0 1 = 0)
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (n : ℕ) (hK : ∀ p r, r < n + 1 → Subsingleton (CategoryTheory.Sheaf.H (K.X p) r)) :
    Function.Injective (CategoryTheory.Sheaf.H.map e (n + 1)) :=
  sheafCohomology_map_succ_injective_of_shortExact
    (AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact K e w haug hpos) n
    (resolutionCycles_cohomology_vanish_below K hpos (n + 1) hK 0 n (by omega))

theorem resolution_firstCohomology_vanish_of_first_differential_injective
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (e : F ⟶ K.X 0) [Mono e] (w : e ≫ K.d 0 1 = 0)
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (n : ℕ) (hK : ∀ p r, r < n + 1 → Subsingleton (CategoryTheory.Sheaf.H (K.X p) r))
    (hd : Function.Injective (CategoryTheory.Sheaf.H.map (K.d 0 1) (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  apply resolution_firstCohomology_injective K e w haug hpos n hK
  apply hd
  rw [map_zero, map_zero, ← CategoryTheory.Sheaf.H.map_comp_apply, w]
  simp only [CategoryTheory.Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ResolutionFirstCohomology.IntrinsicCech
