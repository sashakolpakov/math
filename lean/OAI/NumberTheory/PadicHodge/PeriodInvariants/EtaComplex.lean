import Mathlib

/-! # Eta Complex -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex

noncomputable section

/-!
# The nonnegative eta complex

For a cochain complex C and scalar a, its degree-n term consists of the
elements of a^n C^n whose differential belongs to a^(n+1) C^(n+1).
This file constructs the actual subcomplex, its inclusion, and its action
on cochain maps. No torsion-freeness is needed for these constructions.

Reference: Bhatt--Morrow--Scholze, Integral p-adic Hodge theory, section 6.
https://www.math.uni-bonn.de/people/scholze/integralpadicHodge.pdf
-/

universe u v

open _root_.CategoryTheory

variable {R : Type u} [CommRing R] (a : R)

def scalarPower (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : M →ₗ[R] M :=
  a ^ n • LinearMap.id

def term (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) : Submodule R (C.X n) :=
  LinearMap.range (scalarPower a (C.X n) n) ⊓
    (LinearMap.range (scalarPower a (C.X (n + 1)) (n + 1))).comap (C.d n (n + 1)).hom

theorem mem_term (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : C.X n) :
    x ∈ term a C n ↔
      (∃ y, a ^ n • y = x) ∧ (∃ z, a ^ (n + 1) • z = C.d n (n + 1) x) := Iff.rfl

theorem d_squared (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : C.X n) :
    C.d (n + 1) (n + 1 + 1) (C.d n (n + 1) x) = 0 := by
  have h := congrArg (fun h : C.X n ⟶ C.X (n + 1 + 1) => h x)
    (C.d_comp_d n (n + 1) (n + 1 + 1))
  exact h

def differential (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    term a C n →ₗ[R] term a C (n + 1) where
  toFun x := ⟨C.d n (n + 1) x, x.property.2,
    ⟨0, (smul_zero (a ^ (n + 1 + 1))).trans (d_squared C n x).symm⟩⟩
  map_add' x y := Subtype.ext ((C.d n (n + 1)).hom.map_add x y)
  map_smul' r x := Subtype.ext ((C.d n (n + 1)).hom.map_smul r x)

theorem differential_squared (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (differential a C (n + 1)).comp (differential a C n) = 0 := by
  ext x
  exact d_squared C n x

def eta (C : CochainComplex (ModuleCat.{v} R) ℕ) : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (term a C n))
    (fun n => ModuleCat.ofHom (differential a C n))
    (fun n => ModuleCat.hom_ext (differential_squared a C n))

theorem eta_d (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (eta a C).d n (n + 1) = ModuleCat.ofHom (differential a C n) := by
  change CochainComplex.of.d (fun k => ModuleCat.of R (term a C k))
    (fun k => ModuleCat.ofHom (differential a C k)) n (n + 1) = _
  exact CochainComplex.of_d _ _ n

def inclusion (C : CochainComplex (ModuleCat.{v} R) ℕ) : eta a C ⟶ C :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (term a C n).subtype) (fun n => by
    rw [eta_d]
    rfl)

def componentMap {C D : CochainComplex (ModuleCat.{v} R) ℕ} (f : C ⟶ D) (n : ℕ) :
    term a C n →ₗ[R] term a D n where
  toFun x := ⟨f.f n x, by
    obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := (mem_term a C n x).mp x.property
    constructor
    · refine ⟨f.f n y, ?_⟩
      change a ^ n • f.f n y = f.f n x
      rw [← map_smul, hy]
    · refine ⟨f.f (n + 1) z, ?_⟩
      change a ^ (n + 1) • f.f (n + 1) z = D.d n (n + 1) (f.f n x)
      rw [← map_smul, hz]
      exact (congrArg (fun h : C.X n ⟶ D.X (n + 1) => h x) (f.comm n (n + 1))).symm⟩
  map_add' x y := Subtype.ext ((f.f n).hom.map_add x y)
  map_smul' r x := Subtype.ext ((f.f n).hom.map_smul r x)

def etaMap {C D : CochainComplex (ModuleCat.{v} R) ℕ} (f : C ⟶ D) : eta a C ⟶ eta a D :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (componentMap a f n)) (fun n => by
    rw [eta_d, eta_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun h : C.X n ⟶ D.X (n + 1) => h (x : term a C n).val)
      (f.comm n (n + 1)))

def etaFunctor : CochainComplex (ModuleCat.{v} R) ℕ ⥤ CochainComplex (ModuleCat.{v} R) ℕ where
  obj := eta a
  map := etaMap a
  map_id C := by ext n x; rfl
  map_comp f g := by ext n x; rfl

theorem inclusion_natural {C D : CochainComplex (ModuleCat.{v} R) ℕ} (f : C ⟶ D) :
    etaMap a f ≫ inclusion a D = inclusion a C ≫ f := by
  ext n x
  rfl

def inclusionNatTrans : etaFunctor.{u, v} a ⟶ 𝟭 _ where
  app := inclusion a
  naturality _ _ f := inclusion_natural a f

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex
