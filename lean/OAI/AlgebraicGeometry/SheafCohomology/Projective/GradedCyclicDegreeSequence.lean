import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicSubmodule
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Exact.Basic

/-! # Graded Cyclic Degree Sequence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicDegreeSequence

noncomputable section

/-! The exact sequence in each degree obtained by adjoining one homogeneous generator. -/

open DirectSum
universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M]

def degreeRelations (ℳ : ℤ → Submodule R M) (P : Submodule A M) (d : ℤ) :
    Submodule R (ℳ d) := (P.restrictScalars R).comap (ℳ d).subtype

abbrev DegreeQuotient (ℳ : ℤ → Submodule R M) (P : Submodule A M) (d : ℤ) :=
  (ℳ d) ⧸ degreeRelations ℳ P d

def degreeQuotientMap (ℳ : ℤ → Submodule R M) {P Q : Submodule A M}
    (hPQ : P ≤ Q) (d : ℤ) : DegreeQuotient ℳ P d →ₗ[R] DegreeQuotient ℳ Q d :=
  (degreeRelations ℳ P d).mapQ (degreeRelations ℳ Q d) LinearMap.id
    (fun _ hx => hPQ hx)

theorem degreeQuotientMap_surjective (ℳ : ℤ → Submodule R M) {P Q : Submodule A M}
    (hPQ : P ≤ Q) (d : ℤ) : Function.Surjective (degreeQuotientMap ℳ hPQ d) := by
  intro x
  obtain ⟨m, rfl⟩ := (degreeRelations ℳ Q d).mkQ_surjective x
  exact ⟨(degreeRelations ℳ P d).mkQ m, rfl⟩

variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

def cyclicScalarDegreeMap {m : M} {e : ℤ} (hm : m ∈ ℳ e) (d : ℤ) :
    𝒜 (d - e) →ₗ[R] ℳ d :=
  (((LinearMap.toSpanSingleton A M m).restrictScalars R).comp (𝒜 (d - e)).subtype).codRestrict (ℳ d) (fun a => by
      change a.val • m ∈ ℳ d
      have h : a.val • m ∈ ℳ ((d - e) + e) := SetLike.GradedSMul.smul_mem a.property hm
      simpa only [sub_add_cancel] using h)

def cyclicDegreeInjection (P : Submodule A M) {m : M} {e : ℤ}
    (hm : m ∈ ℳ e) (d : ℤ) :
    DegreeQuotient 𝒜 (GradedCyclicSubmodule.relativeAnnihilator P m) (d - e) →ₗ[R] DegreeQuotient ℳ P d :=
  (degreeRelations 𝒜 (GradedCyclicSubmodule.relativeAnnihilator P m) (d - e)).mapQ
    (degreeRelations ℳ P d) (cyclicScalarDegreeMap 𝒜 ℳ hm d) (fun _ hx => hx)

omit [GradedAlgebra 𝒜] [Decomposition ℳ] in
theorem cyclicDegreeInjection_injective (P : Submodule A M) {m : M} {e : ℤ}
    (hm : m ∈ ℳ e) (d : ℤ) :
    Function.Injective (cyclicDegreeInjection 𝒜 ℳ P hm d) := by
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro x hx
  change x = 0
  obtain ⟨a, rfl⟩ := (degreeRelations 𝒜 (GradedCyclicSubmodule.relativeAnnihilator P m) (d - e)).mkQ_surjective x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change a.val • m ∈ P
  have hxa : (Submodule.Quotient.mk (cyclicScalarDegreeMap 𝒜 ℳ hm d a) :
      DegreeQuotient ℳ P d) = 0 := hx
  exact (Submodule.Quotient.mk_eq_zero (degreeRelations ℳ P d)).mp hxa

theorem cyclicDegreeSequence_exact (P : Submodule A M) (hP : P.IsHomogeneous ℳ)
    {m : M} {e : ℤ} (hm : m ∈ ℳ e) (d : ℤ) :
    Function.Exact (cyclicDegreeInjection 𝒜 ℳ P hm d)
      (degreeQuotientMap ℳ (show P ≤ P ⊔ Submodule.span A {m} from le_sup_left) d) := by
  intro x
  obtain ⟨z, rfl⟩ := (degreeRelations ℳ P d).mkQ_surjective x
  constructor
  · intro hz
    have hzr : (Submodule.Quotient.mk z :
        DegreeQuotient ℳ (P ⊔ Submodule.span A {m}) d) = 0 := hz
    have hz' : z.val ∈ P ⊔ Submodule.span A {m} :=
      (Submodule.Quotient.mk_eq_zero (degreeRelations ℳ (P ⊔ Submodule.span A {m}) d)).mp hzr
    obtain ⟨p, hp, y, hy, hpy⟩ := Submodule.mem_sup.mp hz'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    let a' := decompose 𝒜 a (d - e)
    refine ⟨(degreeRelations 𝒜 (GradedCyclicSubmodule.relativeAnnihilator P m) (d - e)).mkQ a', ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    change a'.val • m - z.val ∈ P
    have h := congrArg (fun t => (decompose ℳ t d).val) hpy
    rw [decompose_add, decompose_of_mem_same ℳ z.property] at h
    change (decompose ℳ p d).val + (decompose ℳ (a • m) d).val = z.val at h
    rw [GradedCyclicSubmodule.homogeneous_smul_component 𝒜 ℳ hm] at h
    change (decompose ℳ p d).val + a'.val • m = z.val at h
    have heq : a'.val • m - z.val = -(decompose ℳ p d).val := by rw [← h]; abel
    rw [heq]
    exact P.neg_mem (hP d hp)
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := (degreeRelations 𝒜 (GradedCyclicSubmodule.relativeAnnihilator P m) (d - e)).mkQ_surjective y
    rw [← hy]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change a.val • m ∈ P ⊔ Submodule.span A {m}
    exact (show Submodule.span A {m} ≤ P ⊔ Submodule.span A {m} from le_sup_right)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicDegreeSequence
