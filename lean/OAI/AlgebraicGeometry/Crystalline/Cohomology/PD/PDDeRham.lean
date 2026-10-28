import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms

/-! # PD De Rham -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham

noncomputable section

/-!
# The completed divided-power de Rham complex

Each term consists of compatible differential forms in the crystalline
inverse system. Differentiation acts coordinatewise. For the p-power
frame tower this is the inverse-limit PD de Rham complex.
-/

open _root_.CategoryTheory Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (B : Type u) [CommRing B] [Algebra k B]
  (F : ℕᵒᵖ ⥤ Thickening.AffinePDThickening p k B)

local notation "W" => WittVector p k
local notation "S" => fun n : ℕ => F.obj (op n)

abbrev Form (q i : ℕ) :=
  DeRham.PDDeRham.Form W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers q

instance formAddCommGroup (q i : ℕ) : AddCommGroup (Form p k B F q i) :=
  inferInstanceAs (AddCommGroup (DeRham.PDDeRham.Form W (S i).ring
    (RingHom.ker (S i).reduction) (S i).dividedPowers q))

instance formModule (q i : ℕ) : Module W (Form p k B F q i) :=
  inferInstanceAs (Module W (DeRham.PDDeRham.Form W (S i).ring
    (RingHom.ker (S i).reduction) (S i).dividedPowers q))

def transition (q n m : ℕ) (h : n ≤ m) : Form p k B F q m →ₗ[W] Form p k B F q n :=
  DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (InverseLimit.PDInverseLimit.transition p k B F n m h).hom)
    (InverseLimit.PDInverseLimit.transition p k B F n m h).dp_comp q

theorem transition_differential (q n m : ℕ) (h : n ≤ m) (ω : Form p k B F q m) :
    transition p k B F (q + 1) n m h
      (DeRham.PDDeRham.differential W (S m).ring (RingHom.ker (S m).reduction) (S m).dividedPowers q ω) =
        DeRham.PDDeRham.differential W (S n).ring (RingHom.ker (S n).reduction) (S n).dividedPowers q
          (transition p k B F q n m h ω) :=
  DeRhamGlobal.PDDeRhamGlobal.formMap_differential
    (CommAlgCat.ofHom (InverseLimit.PDInverseLimit.transition p k B F n m h).hom)
    (InverseLimit.PDInverseLimit.transition p k B F n m h).dp_comp q ω

/-- Compatible forms in one degree of the inverse system. -/
def submodule (q : ℕ) : Submodule W (∀ i : ℕ, Form p k B F q i) where
  carrier x := ∀ n m h, transition p k B F q n m h (x m) = x n
  zero_mem' n m h := map_zero (transition p k B F q n m h)
  add_mem' hx hy n m h := by rw [Pi.add_apply, map_add, hx n m h, hy n m h]; rfl
  smul_mem' w _ hx n m h := by rw [Pi.smul_apply, map_smul, hx n m h]; rfl

abbrev CompletedForm (q : ℕ) := submodule p k B F q

def eval (q i : ℕ) : CompletedForm p k B F q →ₗ[W] Form p k B F q i where
  toFun x := x.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ext {q : ℕ} {x y : CompletedForm p k B F q}
    (h : ∀ i, eval p k B F q i x = eval p k B F q i y) : x = y := Subtype.ext (funext h)

/-- The differential on compatible forms. -/
def differential (q : ℕ) : CompletedForm p k B F q →ₗ[W] CompletedForm p k B F (q + 1) where
  toFun x := ⟨fun i => DeRham.PDDeRham.differential W (S i).ring
    (RingHom.ker (S i).reduction) (S i).dividedPowers q (eval p k B F q i x), by
      intro n m h
      rw [transition_differential]
      exact congrArg (DeRham.PDDeRham.differential W (S n).ring
        (RingHom.ker (S n).reduction) (S n).dividedPowers q) (x.property n m h)⟩
  map_add' x y := PDDeRham.ext p k B F (fun i => map_add (DeRham.PDDeRham.differential W (S i).ring
    (RingHom.ker (S i).reduction) (S i).dividedPowers q) _ _)
  map_smul' w x := PDDeRham.ext p k B F (fun i => (DeRham.PDDeRham.differential W (S i).ring
    (RingHom.ker (S i).reduction) (S i).dividedPowers q).map_smul w _)

@[simp] theorem eval_differential (q i : ℕ) (x : CompletedForm p k B F q) :
    eval p k B F (q + 1) i (differential p k B F q x) =
      DeRham.PDDeRham.differential W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers q
        (eval p k B F q i x) := rfl

theorem differential_square (q : ℕ) (x : CompletedForm p k B F q) :
    differential p k B F (q + 1) (differential p k B F q x) = 0 := by
  apply PDDeRham.ext p k B F
  intro i
  rw [eval_differential, eval_differential, map_zero]
  exact DeRham.PDDeRham.differential_square W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers q _

/-- The inverse-limit divided-power de Rham complex. -/
def complex : CochainComplex (ModuleCat.{u} W) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of W (CompletedForm p k B F q))
    (fun q => ModuleCat.ofHom (differential p k B F q))
    (fun q => ModuleCat.hom_ext (LinearMap.ext (differential_square p k B F q)))

def evaluation (i : ℕ) : complex p k B F ⟶
    DeRham.PDDeRham.complex W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers where
  f q := ModuleCat.ofHom (eval p k B F q i)
  comm' n m h := by
    change n + 1 = m at h
    subst m
    dsimp only [complex, DeRham.PDDeRham.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (eval_differential p k B F n i)

def zeroEquiv (i : ℕ) : Form p k B F 0 i ≃ₗ[W] (S i).ring :=
  (DeRham.PDDeRham.degreeZeroEquiv W (S i).ring (RingHom.ker (S i).reduction)
    (S i).dividedPowers).restrictScalars W

theorem zeroEquiv_transition (n m : ℕ) (h : n ≤ m) (ω : Form p k B F 0 m) :
    zeroEquiv p k B F n (transition p k B F 0 n m h ω) =
      (InverseLimit.PDInverseLimit.transition p k B F n m h).hom (zeroEquiv p k B F m ω) := by
  have hω := DeRham.PDDeRham.symbol_degreeZeroEquiv W (S m).ring
    (RingHom.ker (S m).reduction) (S m).dividedPowers ω
  rw [← hω]
  change DeRham.PDDeRham.degreeZeroEquiv _ _ _ _
    (DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (InverseLimit.PDInverseLimit.transition p k B F n m h).hom)
      (InverseLimit.PDInverseLimit.transition p k B F n m h).dp_comp 0 (DeRham.PDDeRham.symbol _ _ _ _ _ _)) =
        (InverseLimit.PDInverseLimit.transition p k B F n m h).hom
          (DeRham.PDDeRham.degreeZeroEquiv _ _ _ _ (DeRham.PDDeRham.symbol _ _ _ _ _ _))
  rw [DeRhamGlobal.PDDeRhamGlobal.formMap_symbol, DeRham.PDDeRham.degreeZeroEquiv_symbol, DeRham.PDDeRham.degreeZeroEquiv_symbol]
  rfl

/-- A compatible zero-form gives a compatible system of ambient functions. -/
def toFunctions : CompletedForm p k B F 0 →ₗ[W] InverseLimit.PDInverseLimit.Ring p k B F where
  toFun x := ⟨fun i => zeroEquiv p k B F i (eval p k B F 0 i x), by
    intro n m h
    exact (zeroEquiv_transition p k B F n m h _).symm.trans
      (congrArg (zeroEquiv p k B F n) (x.property n m h))⟩
  map_add' x y := InverseLimit.PDInverseLimit.ext p k B F (fun i => (zeroEquiv p k B F i).map_add _ _)
  map_smul' w x := InverseLimit.PDInverseLimit.ext p k B F (fun i => (zeroEquiv p k B F i).map_smul w _)

/-- Compatible functions are zero-forms, coordinate by coordinate. -/
def fromFunctions : InverseLimit.PDInverseLimit.Ring p k B F →ₗ[W] CompletedForm p k B F 0 where
  toFun x := ⟨fun i => (zeroEquiv p k B F i).symm (InverseLimit.PDInverseLimit.eval p k B F i x), by
    intro n m h
    apply (zeroEquiv p k B F n).injective
    rw [zeroEquiv_transition, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact InverseLimit.PDInverseLimit.eval_compatible p k B F n m h x⟩
  map_add' x y := PDDeRham.ext p k B F (fun i => (zeroEquiv p k B F i).symm.map_add _ _)
  map_smul' w x := PDDeRham.ext p k B F (fun i => (zeroEquiv p k B F i).symm.map_smul w _)

/-- Degree zero of the completed de Rham complex is the inverse-limit ring. -/
def degreeZeroEquiv : CompletedForm p k B F 0 ≃ₗ[W] InverseLimit.PDInverseLimit.Ring p k B F :=
  LinearEquiv.ofLinearMap (toFunctions p k B F) (fromFunctions p k B F)
    (by
      apply LinearMap.ext
      intro x
      exact InverseLimit.PDInverseLimit.ext p k B F (fun i => (zeroEquiv p k B F i).apply_symm_apply _))
    (by
      apply LinearMap.ext
      intro x
      exact PDDeRham.ext p k B F (fun i => (zeroEquiv p k B F i).symm_apply_apply _))

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B F

theorem transition_smul (q n m : ℕ) (h : n ≤ m) (a : (S m).ring) (ω : Form p k B F q m) :
    transition p k B F q n m h (a • ω) =
      (InverseLimit.PDInverseLimit.transition p k B F n m h).hom a • transition p k B F q n m h ω :=
  DeRhamGlobal.PDDeRhamGlobal.formMap_smul
    (CommAlgCat.ofHom (InverseLimit.PDInverseLimit.transition p k B F n m h).hom)
    (InverseLimit.PDInverseLimit.transition p k B F n m h).dp_comp q a ω

/-- Completed forms carry the coordinatewise action of the inverse-limit ring. -/
instance completedSMul (q : ℕ) : SMul C (CompletedForm p k B F q) where
  smul a x := ⟨fun i => InverseLimit.PDInverseLimit.eval p k B F i a • eval p k B F q i x, by
    intro n m h
    rw [transition_smul, InverseLimit.PDInverseLimit.eval_compatible]
    exact congrArg (InverseLimit.PDInverseLimit.eval p k B F n a • ·) (x.property n m h)⟩

@[simp] theorem eval_smul (q i : ℕ) (a : C) (x : CompletedForm p k B F q) :
    eval p k B F q i (a • x) = InverseLimit.PDInverseLimit.eval p k B F i a • eval p k B F q i x := rfl

instance completedModule (q : ℕ) : Module C (CompletedForm p k B F q) where
  one_smul x := PDDeRham.ext p k B F (fun i => by
    change InverseLimit.PDInverseLimit.eval p k B F i 1 • eval p k B F q i x = _
    rw [map_one]
    exact one_smul (S i).ring (eval p k B F q i x))
  mul_smul a b x := PDDeRham.ext p k B F (fun i => by
    change InverseLimit.PDInverseLimit.eval p k B F i (a * b) • eval p k B F q i x =
      InverseLimit.PDInverseLimit.eval p k B F i a • (InverseLimit.PDInverseLimit.eval p k B F i b • eval p k B F q i x)
    rw [map_mul]
    exact mul_smul _ _ _)
  smul_zero a := PDDeRham.ext p k B F (fun i => by simp only [eval_smul, map_zero, smul_zero])
  smul_add a x y := PDDeRham.ext p k B F (fun i => by simp only [eval_smul, map_add, smul_add])
  add_smul a b x := PDDeRham.ext p k B F (fun i => by simp only [eval_smul, map_add, add_smul])
  zero_smul x := PDDeRham.ext p k B F (fun i => by simp only [eval_smul, map_zero, zero_smul])

theorem differential_zero_symm (i : ℕ) (a : (S i).ring) :
    DeRham.PDDeRham.differential W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers 0
      ((zeroEquiv p k B F i).symm a) =
        OneForms.PDOneForms.D W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers a := by
  have h : (zeroEquiv p k B F i).symm a =
      DeRham.PDDeRham.symbol W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers a
        (fun j : Fin 0 => j.elim0) := by
    apply (zeroEquiv p k B F i).injective
    exact ((zeroEquiv p k B F i).apply_symm_apply a).trans
      (DeRham.PDDeRham.degreeZeroEquiv_symbol W (S i).ring (RingHom.ker (S i).reduction)
        (S i).dividedPowers a (fun j : Fin 0 => j.elim0)).symm
  rw [h]
  change DeRham.PDDeRham.differential W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers 0
    ((DeRham.PDDeRham.relations W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers 0).mkQ
      (DeRhamPresentationTo.DeRhamPresentation.symbol W (S i).ring a (fun j : Fin 0 => j.elim0))) = _
  rw [DeRham.PDDeRham.differential_mk, DeRhamPresentationTo.DeRhamPresentation.differential_symbol]
  rfl

/-- Exterior differentiation viewed as a map out of the inverse-limit ring. -/
def differentialRing : C →ₗ[W] CompletedForm p k B F 1 :=
  (differential p k B F 0).comp (degreeZeroEquiv p k B F).symm.toLinearMap

@[simp] theorem eval_differentialRing (i : ℕ) (a : C) :
    eval p k B F 1 i (differentialRing p k B F a) =
      OneForms.PDOneForms.D W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers
        (InverseLimit.PDInverseLimit.eval p k B F i a) :=
  differential_zero_symm p k B F i (InverseLimit.PDInverseLimit.eval p k B F i a)

/-- The derivation on compatible sections induced by the finite-level derivations. -/
def derivation : Derivation W C (CompletedForm p k B F 1) where
  __ := differentialRing p k B F
  map_one_eq_zero' := by
    apply PDDeRham.ext p k B F
    intro i
    change eval p k B F 1 i (differentialRing p k B F 1) = _
    rw [eval_differentialRing, map_one, map_zero, Derivation.map_one_eq_zero]
  leibniz' a b := by
    apply PDDeRham.ext p k B F
    intro i
    change eval p k B F 1 i (differentialRing p k B F (a * b)) = _
    simp only [eval_differentialRing, map_mul, Derivation.leibniz, map_add, eval_smul]

theorem derivation_dpow (n : ℕ) {x : C} (hx : x ∈ RingHom.ker (InverseLimit.PDInverseLimit.reduction p k B F)) :
    derivation p k B F ((InverseLimit.PDInverseLimit.dividedPowers p k B F).dpow (n + 1) x) =
      (InverseLimit.PDInverseLimit.dividedPowers p k B F).dpow n x • derivation p k B F x := by
  apply PDDeRham.ext p k B F
  intro i
  change eval p k B F 1 i (differentialRing p k B F
    (InverseLimit.PDInverseLimit.dpow p k B F (n + 1) x)) =
      eval p k B F 1 i (InverseLimit.PDInverseLimit.dpow p k B F n x • differentialRing p k B F x)
  rw [eval_differentialRing, eval_smul, eval_differentialRing,
    InverseLimit.PDInverseLimit.eval_dpow p k B F (n + 1) i hx, InverseLimit.PDInverseLimit.eval_dpow p k B F n i hx]
  exact OneForms.PDOneForms.D_dpow W (S i).ring (RingHom.ker (S i).reduction) (S i).dividedPowers n
    (InverseLimit.PDInverseLimit.eval_mem_kernel p k B F i hx)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham
