import OAI.AlgebraicGeometry.Comparison.Betti.ExtVanishing
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Resolution Cycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionCycles.Ext

noncomputable section

/-! Cycle sequences and dimension shifting for an actual augmented acyclic resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) (K : CochainComplex C ℕ)

abbrev resolutionSequence (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2)) (K.d_comp_d n (n + 1) (n + 2))

variable {F : C} (e : F ⟶ K.X 0) (w : e ≫ K.d 0 1 = 0)

abbrev initialCycleSequence : ShortComplex C :=
  let T := resolutionSequence K 0
  ShortComplex.mk e T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp]
    exact w)

omit [HasExt C] in
theorem initialCycleSequence_shortExact [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (resolutionSequence K n).Exact) :
    (initialCycleSequence K e w).ShortExact := by
  let T := resolutionSequence K 0
  let S := initialCycleSequence K e w
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T.iCycles T.f haug.fIsKernel S.zero T.toCycles_i
  have : Epi S.g := (hpos 0).epi_toCycles
  exact { exact := ShortComplex.exact_of_f_is_kernel S hk }

abbrev successiveCycleSequence (n : ℕ) : ShortComplex C :=
  let T := resolutionSequence K n
  let T' := resolutionSequence K (n + 1)
  ShortComplex.mk T.iCycles T'.toCycles (by
    rw [← cancel_mono T'.iCycles, Category.assoc, T'.toCycles_i, zero_comp]
    exact T.iCycles_g)

omit [HasExt C] in
theorem successiveCycleSequence_shortExact (hpos : ∀ n, (resolutionSequence K n).Exact) (n : ℕ) :
    (successiveCycleSequence K n).ShortExact := by
  let T := resolutionSequence K n
  let T' := resolutionSequence K (n + 1)
  let S := successiveCycleSequence K n
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T'.iCycles T'.f T.cyclesIsKernel S.zero T'.toCycles_i
  have : Epi S.g := (hpos (n + 1)).epi_toCycles
  exact { exact := ShortComplex.exact_of_f_is_kernel S hk }

theorem resolutionCycles_ext_vanish [Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (resolutionSequence K n).Exact)
    (hF : ∀ q, Subsingleton (Ext A F (q + 1)))
    (hK : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (n q : ℕ) :
    Subsingleton (Ext A (resolutionSequence K n).cycles (q + 1)) := by
  induction n generalizing q with
  | zero =>
    have : Subsingleton (Ext A (K.X 0) (q + 1)) := hK 0 q
    have : Subsingleton (Ext A F ((q + 1) + 1)) := hF (q + 1)
    exact ExtVanishing.right_ext_subsingleton A (initialCycleSequence_shortExact K e w haug hpos) (q + 1)
  | succ n ih =>
    have : Subsingleton (Ext A (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    have : Subsingleton (Ext A (resolutionSequence K n).cycles ((q + 1) + 1)) := ih (q + 1)
    exact ExtVanishing.right_ext_subsingleton A (successiveCycleSequence_shortExact K hpos n) (q + 1)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.ResolutionCycles.Ext
