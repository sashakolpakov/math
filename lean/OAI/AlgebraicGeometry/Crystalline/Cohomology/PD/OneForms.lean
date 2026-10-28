import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # One Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms

noncomputable section

/-!
# Universal property of the divided-power one-forms

Degree one of the previously constructed PD de Rham complex represents
derivations satisfying `d γₙ₊₁(x) = γₙ(x) dx`.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

def ordinaryD : Derivation R A (DeRhamPresentationTo.DeRhamPresentation.Form R A 1) where
  __ := DeRhamPresentationTo.DeRhamPresentation.generatorDifferential R A (fun i : Fin 0 => i.elim0)
  map_one_eq_zero' := DeRhamPresentationTo.DeRhamPresentation.symbol_cons_one R A _
  leibniz' a b := DeRhamPresentationTo.DeRhamPresentation.symbol_cons_mul R A a b _

/-- Universal divided-power derivation into degree one of the PD complex. -/
def D : Derivation R A (DeRham.PDDeRham.Form R A I δ 1) :=
  (DeRham.PDDeRham.relations R A I δ 1).mkQ.compDer (ordinaryD R A)

@[simp] theorem D_apply (a : A) :
    D R A I δ a = DeRham.PDDeRham.symbol R A I δ 1 (fun _ : Fin 1 => a) := by
  change DeRham.PDDeRham.symbol R A I δ 1 (Fin.cons a (fun i : Fin 0 => i.elim0)) = _
  congr 1
  funext i
  fin_cases i
  rfl

theorem D_dpow (n : ℕ) {x : A} (hx : x ∈ I) :
    D R A I δ (δ.dpow (n + 1) x) = δ.dpow n x • D R A I δ x := by
  have h := DeRham.PDDeRham.symbol_update_dpow R A I δ (fun _ : Fin 1 => 0) 0 ⟨x, hx⟩ n
  have hu (a : A) : Function.update (fun _ : Fin 1 => (0 : A)) 0 a = fun _ => a := by
    funext i
    fin_cases i
    simp
  simpa only [hu, D_apply] using h

variable (M : Type u) [AddCommGroup M] [Module A M] [Module R M]
  (d : Derivation R A M)

def rawLift : DeRhamPresentationTo.DeRhamPresentation.Raw A 1 →ₗ[A] M :=
  Finsupp.linearCombination A (fun v : Fin 1 → A => d (v 0))

@[simp] theorem rawLift_single (a : A) (v : Fin 1 → A) :
    rawLift R A M d (Finsupp.single v a) = a • d (v 0) := by
  simp [rawLift]

theorem rawLift_relation (r : DeRhamPresentationTo.DeRhamPresentation.RelationIndex R A 1) :
    rawLift R A M d (DeRhamPresentationTo.DeRhamPresentation.relation R A 1 r) = 0 := by
  cases r with
  | add v i x y =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [DeRhamPresentationTo.DeRhamPresentation.relation, map_sub, rawLift_single, map_add]
  | mul v i x y =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [DeRhamPresentationTo.DeRhamPresentation.relation, map_sub, rawLift_single, d.leibniz]
  | base v i r =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [DeRhamPresentationTo.DeRhamPresentation.relation, rawLift_single]
  | alt v i j hij hne => exact (hne (Subsingleton.elim i j)).elim

def ordinaryLift : DeRhamPresentationTo.DeRhamPresentation.Form R A 1 →ₗ[A] M :=
  (DeRhamPresentationTo.DeRhamPresentation.relations R A 1).liftQ (rawLift R A M d)
    (Submodule.span_le.mpr (by
      rintro _ ⟨r, rfl⟩
      exact rawLift_relation R A M d r))

@[simp] theorem ordinaryLift_symbol (a : A) (v : Fin 1 → A) :
    ordinaryLift R A M d (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a • d (v 0) :=
  rawLift_single R A M d a v

variable (hd : ∀ n x, x ∈ I → d (δ.dpow (n + 1) x) = δ.dpow n x • d x)

include hd in
theorem ordinaryLift_relation (r : DeRham.PDDeRham.RelationIndex A I 1) :
    ordinaryLift R A M d (DeRham.PDDeRham.relation R A I δ 1 r) = 0 := by
  have hi : r.i = 0 := Subsingleton.elim _ _
  simp only [DeRham.PDDeRham.relation, map_sub, ordinaryLift_symbol, hi,
    Function.update_self, one_smul, hd r.m r.x r.x.property, sub_self]

/-- The linear map represented by a divided-power derivation. -/
def lift : DeRham.PDDeRham.Form R A I δ 1 →ₗ[A] M :=
  (DeRham.PDDeRham.relations R A I δ 1).liftQ (ordinaryLift R A M d)
    (Submodule.span_le.mpr (by
      rintro _ ⟨r, rfl⟩
      exact ordinaryLift_relation R A I δ M d hd r))

@[simp] theorem lift_symbol (a : A) (v : Fin 1 → A) :
    lift R A I δ M d hd (DeRham.PDDeRham.symbol R A I δ a v) = a • d (v 0) :=
  ordinaryLift_symbol R A M d a v

@[simp] theorem lift_D (a : A) :
    lift R A I δ M d hd (D R A I δ a) = d a := by
  rw [D_apply, lift_symbol, one_smul]

omit [Module R M] in
theorem linearMap_ext (f g : DeRham.PDDeRham.Form R A I δ 1 →ₗ[A] M)
    (h : ∀ a, f (D R A I δ a) = g (D R A I δ a)) : f = g := by
  apply LinearMap.ext
  intro ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δ 1) ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A 1) ω
  induction ω using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v a =>
    change f (DeRham.PDDeRham.symbol R A I δ a v) = g (DeRham.PDDeRham.symbol R A I δ a v)
    have hv : v = fun _ : Fin 1 => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
    rw [DeRham.PDDeRham.symbol_smul_one, hv, ← D_apply, map_smul, map_smul, h]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms
