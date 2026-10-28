import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Surjective Quasi Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso

noncomputable section

/-!
# Primitives in the kernel of a surjective quasi-isomorphism

For actual module-valued cochain complexes, a degreewise surjective
quasi-isomorphism has an acyclic categorical kernel. A closed cochain killed
by the morphism therefore has a primitive killed by the same morphism. In
degree zero every such closed cochain is zero.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R : Type} [Ring R]
variable {K L : CochainComplex (ModuleCat.{0} R) ℕ}

/-- The actual categorical kernel sequence of a module cochain morphism. -/
def cochainKernelSequence (f : K ⟶ L) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk (kernel.ι f) f (kernel.condition f)

/-- Degreewise surjectivity makes the actual kernel sequence short exact. -/
theorem cochainKernelSequence_shortExact (f : K ⟶ L)
    (hsurj : ∀ n, Function.Surjective (f.f n)) :
    (cochainKernelSequence f).ShortExact := by
  have : Epi f := HomologicalComplex.epi_of_epi_f f
    (fun n => (ModuleCat.epi_iff_surjective _).2 (hsurj n))
  change (ShortComplex.mk (kernel.ι f) f _).ShortExact
  exact { exact := ShortComplex.kernelSequence_exact f }

/-- The long exact cohomology sequence proves that the genuine kernel complex
of a degreewise surjective quasi-isomorphism is acyclic. -/
theorem cochainKernel_acyclic_of_surjective_quasiIso (f : K ⟶ L) [QuasiIso f]
    (hsurj : ∀ n, Function.Surjective (f.f n)) : (kernel f).Acyclic :=
  (cochainKernelSequence_shortExact f hsurj).acyclic_X₁ (show QuasiIso f from inferInstance)

/-- Conversely, a degreewise surjective map with acyclic actual kernel is a
quasi-isomorphism. The two adjacent pieces of the long exact sequence give
injectivity and surjectivity on each cohomology group. -/
theorem quasiIso_of_surjective_of_acyclic_kernel (f : K ⟶ L)
    (hsurj : ∀ n, Function.Surjective (f.f n)) (hker : (kernel f).Acyclic) :
    QuasiIso f := by
  have hS := cochainKernelSequence_shortExact f hsurj
  constructor
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap f n).2
  have : Mono (HomologicalComplex.homologyMap f n) :=
    (hS.homology_exact₂ n).mono_g ((hker n).isZero_homology.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap f n) :=
    (hS.homology_exact₃ n (n + 1) rfl).epi_f
      ((hker (n + 1)).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- For a degreewise surjective map of actual module cochain complexes,
acyclicity of the actual kernel is equivalent to being a quasi-isomorphism. -/
theorem quasiIso_iff_acyclic_kernel_of_surjective (f : K ⟶ L)
    (hsurj : ∀ n, Function.Surjective (f.f n)) :
    QuasiIso f ↔ (kernel f).Acyclic := by
  constructor
  · intro h
    exact cochainKernel_acyclic_of_surjective_quasiIso f hsurj
  · exact quasiIso_of_surjective_of_acyclic_kernel f hsurj

/-- The degreewise image of the categorical kernel inclusion is the ordinary
linear-map kernel. No surjectivity hypothesis is needed for this identification. -/
theorem cochainKernelInclusion_range (f : K ⟶ L) (n : ℕ) :
    LinearMap.range ((kernel.ι f).f n).hom = LinearMap.ker (f.f n).hom := by
  have h : (cochainKernelSequence f).Exact := ShortComplex.kernelSequence_exact f
  exact (h.map (HomologicalComplex.eval (ModuleCat.{0} R)
    (ComplexShape.up ℕ) n)).moduleCat_range_eq_ker

/-- A closed cochain killed by the morphism lifts to a closed cochain in its
actual categorical kernel complex. -/
theorem exists_closed_cochainKernel_lift (f : K ⟶ L) (n : ℕ)
    (c : K.X n) (hc : K.d n (n + 1) c = 0) (hfc : f.f n c = 0) :
    ∃ z : (kernel f).X n, (kernel.ι f).f n z = c ∧
      (kernel f).d n (n + 1) z = 0 := by
  have hmem : c ∈ LinearMap.range ((kernel.ι f).f n).hom := by
    rw [cochainKernelInclusion_range]
    exact hfc
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, hz, ?_⟩
  apply (ModuleCat.mono_iff_injective ((kernel.ι f).f (n + 1))).1 inferInstance
  rw [map_zero]
  have h := ConcreteCategory.congr_hom ((kernel.ι f).comm n (n + 1)) z
  change K.d n (n + 1) ((kernel.ι f).f n z) =
    (kernel.ι f).f (n + 1) ((kernel f).d n (n + 1) z) at h
  exact h.symm.trans (by rw [hz, hc])

/-- Exactness in a positive degree produces an actual lower-degree primitive. -/
theorem exists_cochainPrimitive_of_exactAt_succ (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (hK : K.ExactAt (n + 1))
    (c : K.X (n + 1)) (hc : K.d (n + 1) (n + 2) c = 0) :
    ∃ b : K.X n, K.d n (n + 1) b = c := by
  have h : (K.sc' n (n + 1) (n + 2)).Exact :=
    (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)).1 hK
  exact (ShortComplex.moduleCat_exact_iff _).1 h c hc

/-- Since a nonnegative cochain complex has no incoming differential in
degree zero, exactness there forces every closed zero-cochain to vanish. -/
theorem cochain_eq_zero_of_exactAt_zero (K : CochainComplex (ModuleCat.{0} R) ℕ)
    (hK : K.ExactAt 0) (c : K.X 0) (hc : K.d 0 1 c = 0) : c = 0 := by
  have h : (K.sc' 0 0 1).Exact :=
    (K.exactAt_iff' 0 0 1 (by simp) (by simp)).1 hK
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).1 h c hc
  change K.d 0 0 b = c at hb
  rw [K.shape 0 0 (by simp)] at hb
  exact hb.symm.trans (by rfl)

/-- A closed cochain in the kernel of a degreewise surjective quasi-isomorphism
has a primitive in the same kernel, with both equalities stated in the original
cochain complex. -/
theorem exists_primitive_in_kernel_of_surjective_quasiIso
    (f : K ⟶ L) [QuasiIso f] (hsurj : ∀ n, Function.Surjective (f.f n))
    (n : ℕ) (c : K.X (n + 1)) (hc : K.d (n + 1) (n + 2) c = 0)
    (hfc : f.f (n + 1) c = 0) :
    ∃ b : K.X n, K.d n (n + 1) b = c ∧ f.f n b = 0 := by
  obtain ⟨z, hz, hclosed⟩ := exists_closed_cochainKernel_lift f (n + 1) c hc hfc
  obtain ⟨w, hw⟩ := exists_cochainPrimitive_of_exactAt_succ (kernel f) n
    (cochainKernel_acyclic_of_surjective_quasiIso f hsurj (n + 1)) z hclosed
  refine ⟨(kernel.ι f).f n w, ?_, ?_⟩
  · have h := ConcreteCategory.congr_hom ((kernel.ι f).comm n (n + 1)) w
    change K.d n (n + 1) ((kernel.ι f).f n w) =
      (kernel.ι f).f (n + 1) ((kernel f).d n (n + 1) w) at h
    exact h.trans (by rw [hw, hz])
  · exact ConcreteCategory.congr_hom
      (congrArg (fun g => g.f n) (kernel.condition f)) w

/-- The degree-zero part: a closed zero-cochain killed by a degreewise
surjective quasi-isomorphism is zero. -/
theorem cochain_eq_zero_in_kernel_of_surjective_quasiIso
    (f : K ⟶ L) [QuasiIso f] (hsurj : ∀ n, Function.Surjective (f.f n))
    (c : K.X 0) (hc : K.d 0 1 c = 0) (hfc : f.f 0 c = 0) : c = 0 := by
  obtain ⟨z, hz, hclosed⟩ := exists_closed_cochainKernel_lift f 0 c hc hfc
  have hz0 := cochain_eq_zero_of_exactAt_zero (kernel f)
    (cochainKernel_acyclic_of_surjective_quasiIso f hsurj 0) z hclosed
  rw [hz0, map_zero] at hz
  exact hz.symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso
