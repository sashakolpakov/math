import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Double Complex Quasi Iso -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexQuasiIso.DoubleComplex

noncomputable section

/-!
# Element criteria for quasi-isomorphisms of module complexes

These lemmas concern mathlib's actual homology objects and homology maps. The
proof uses its canonical kernel/image quotient isomorphism; the hypotheses
describe cocycle lifting and boundary reflection, rather than assuming any
isomorphism on cohomology. Both the ring and module universes are arbitrary.
-/

open _root_.CategoryTheory

universe u v w

variable {R : Type u} [Ring R]

section ShortComplex

variable {S T : ShortComplex (ModuleCat.{v} R)}

private def kernelClass (S : ShortComplex (ModuleCat.{v} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
    (LinearMap.range S.moduleCatToCycles).mkQ

private theorem kernelClass_surjective (S : ShortComplex (ModuleCat.{v} R)) :
    Function.Surjective (kernelClass S) :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
    (LinearMap.range S.moduleCatToCycles).mkQ_surjective

set_option backward.isDefEq.respectTransparency false in
private theorem kernelClass_eq_iff_exists (S : ShortComplex (ModuleCat.{v} R))
    (x y : LinearMap.ker S.g.hom) :
    kernelClass S x = kernelClass S y ↔
      ∃ z : S.X₁, S.f z = (x : S.X₂) - (y : S.X₂) := by
  change S.moduleCatHomologyIso.toLinearEquiv.symm
      ((LinearMap.range S.moduleCatToCycles).mkQ x) =
    S.moduleCatHomologyIso.toLinearEquiv.symm
      ((LinearMap.range S.moduleCatToCycles).mkQ y) ↔ _
  rw [S.moduleCatHomologyIso.toLinearEquiv.symm.injective.eq_iff]
  change (Submodule.Quotient.mk x :
      LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) =
    Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq]
  change (∃ z, S.moduleCatToCycles z = x - y) ↔ _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩

private theorem kernelClass_eq_zero_iff_exists (S : ShortComplex (ModuleCat.{v} R))
    (x : LinearMap.ker S.g.hom) :
    kernelClass S x = 0 ↔ ∃ z : S.X₁, S.f z = (x : S.X₂) := by
  simpa using kernelClass_eq_iff_exists S x 0

private def kernelMap (φ : S ⟶ T) :
    LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ fun x => by
    change T.g (φ.τ₂ (x : S.X₂)) = 0
    have h := ConcreteCategory.congr_hom φ.comm₂₃ (x : S.X₂)
    change T.g (φ.τ₂ (x : S.X₂)) = φ.τ₃ (S.g (x : S.X₂)) at h
    exact h.trans (by rw [show S.g (x : S.X₂) = 0 from x.property, map_zero])

private theorem kernelClass_eq_homologyπ (S : ShortComplex (ModuleCat.{v} R))
    (x : LinearMap.ker S.g.hom) :
    kernelClass S x = S.homologyπ (S.moduleCatCyclesIso.inv x) := by
  exact (ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π x).symm

private theorem kernelMap_eq_cyclesMap (φ : S ⟶ T)
    (x : LinearMap.ker S.g.hom) :
    T.moduleCatCyclesIso.inv (kernelMap φ x) =
      (ShortComplex.cyclesMap φ) (S.moduleCatCyclesIso.inv x) := by
  apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
  have hT := ConcreteCategory.congr_hom T.moduleCatCyclesIso_inv_iCycles (kernelMap φ x)
  have hS := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles x
  have hφ := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ)
    (S.moduleCatCyclesIso.inv x)
  change T.iCycles (T.moduleCatCyclesIso.inv (kernelMap φ x)) = φ.τ₂ (x : S.X₂) at hT
  change S.iCycles (S.moduleCatCyclesIso.inv x) = (x : S.X₂) at hS
  change T.iCycles ((ShortComplex.cyclesMap φ) (S.moduleCatCyclesIso.inv x)) =
    φ.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv x)) at hφ
  exact hT.trans (by rw [hS] at hφ; exact hφ.symm)

private theorem kernelClass_naturality (φ : S ⟶ T)
    (x : LinearMap.ker S.g.hom) :
    (ShortComplex.homologyMap φ) (kernelClass S x) = kernelClass T (kernelMap φ x) := by
  rw [kernelClass_eq_homologyπ, kernelClass_eq_homologyπ, kernelMap_eq_cyclesMap]
  exact ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ)
    (S.moduleCatCyclesIso.inv x)

/-- Lifting every target cycle modulo an actual boundary makes the canonical
homology map surjective. -/
theorem shortComplex_homologyMap_surjective_of_cycle_lift (φ : S ⟶ T)
    (hlift : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x - y) :
    Function.Surjective (ShortComplex.homologyMap φ) := by
  intro a
  obtain ⟨y, rfl⟩ := kernelClass_surjective T a
  obtain ⟨x, hx, z, hz⟩ := hlift y y.property
  refine ⟨kernelClass S ⟨x, hx⟩, ?_⟩
  rw [kernelClass_naturality]
  exact (kernelClass_eq_iff_exists T _ y).mpr ⟨z, hz⟩

/-- A cycle whose image is a boundary is itself a boundary precisely in the
situation needed to make the canonical homology map injective. -/
theorem shortComplex_homologyMap_injective_of_boundary_reflection (φ : S ⟶ T)
    (hreflect : ∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) :
    Function.Injective (ShortComplex.homologyMap φ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨x, rfl⟩ := kernelClass_surjective S a
  rw [kernelClass_naturality] at ha
  apply (kernelClass_eq_zero_iff_exists S x).mpr
  exact hreflect x x.property ((kernelClass_eq_zero_iff_exists T _).mp ha)

/-- An elementwise criterion for quasi-isomorphisms of short complexes of
modules, with no presumed comparison isomorphism. -/
theorem shortComplex_quasiIso_of_cycle_lift_and_boundary_reflection (φ : S ⟶ T)
    (hlift : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = φ.τ₂ x - y)
    (hreflect : ∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) :
    ShortComplex.QuasiIso φ := by
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  exact ⟨shortComplex_homologyMap_injective_of_boundary_reflection φ hreflect,
    shortComplex_homologyMap_surjective_of_cycle_lift φ hlift⟩

end ShortComplex

variable {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) c}

/-- The same elementwise criterion in any degree and any complex shape. The
shape predecessor correctly includes the zero incoming map at an endpoint. -/
theorem quasiIsoAt_of_cycle_lift_and_boundary_reflection (f : K ⟶ L) (n : ι)
    (hlift : ∀ y : L.X n, L.d n (c.next n) y = 0 →
      ∃ x : K.X n, K.d n (c.next n) x = 0 ∧
        ∃ z : L.X (c.prev n), L.d (c.prev n) n z = f.f n x - y)
    (hreflect : ∀ x : K.X n, K.d n (c.next n) x = 0 →
      (∃ z : L.X (c.prev n), L.d (c.prev n) n z = f.f n x) →
        ∃ z : K.X (c.prev n), K.d (c.prev n) n z = x) :
    QuasiIsoAt f n := by
  rw [quasiIsoAt_iff]
  exact shortComplex_quasiIso_of_cycle_lift_and_boundary_reflection
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) hlift hreflect

/-- Cycle lifting modulo boundaries together with boundary reflection in
every degree proves a quasi-isomorphism of the actual module complexes. -/
theorem quasiIso_of_cycle_lift_and_boundary_reflection (f : K ⟶ L)
    (hlift : ∀ (n : ι) (y : L.X n), L.d n (c.next n) y = 0 →
      ∃ x : K.X n, K.d n (c.next n) x = 0 ∧
        ∃ z : L.X (c.prev n), L.d (c.prev n) n z = f.f n x - y)
    (hreflect : ∀ (n : ι) (x : K.X n), K.d n (c.next n) x = 0 →
      (∃ z : L.X (c.prev n), L.d (c.prev n) n z = f.f n x) →
        ∃ z : K.X (c.prev n), K.d (c.prev n) n z = x) :
    QuasiIso f := by
  rw [quasiIso_iff]
  exact fun n => quasiIsoAt_of_cycle_lift_and_boundary_reflection f n (hlift n) (hreflect n)

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexQuasiIso.DoubleComplex
