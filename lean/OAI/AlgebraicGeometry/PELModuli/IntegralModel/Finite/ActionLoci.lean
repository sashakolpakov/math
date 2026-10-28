import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EquationLoci
import Mathlib.Algebra.Category.Ring.Basic

/-! # Action Loci -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ActionLoci

noncomputable section

/-! The finite multiplication-table action locus in a represented ring
functor. The closed parameter scheme is constructed from actual finite
equations. This supplies the ring-action part of the PEL parameter problem;
it does not assert that the entire PEL functor is already represented. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Module Opposite

universe u

theorem basisExtension_map {R V W : Type*} [Ring R] [Ring V] [Ring W]
    {Idx : Type*} (b : Basis Idx ℤ R) (v : Idx → V) (f : V →+* W) (x : R) :
    f (Actions.basisExtension b v x) = Actions.basisExtension b (fun i => f (v i)) x := by
  have h : f.toAddMonoidHom.toIntLinearMap.comp (Actions.basisExtension b v) =
      Actions.basisExtension b (fun i => f (v i)) := b.ext fun i => by
    change f (Actions.basisExtension b v (b i)) = Actions.basisExtension b (fun i => f (v i)) (b i)
    rw [Actions.basisExtension_basis, Actions.basisExtension_basis]
  exact LinearMap.congr_fun h x

namespace FiniteActionLocus

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ RingCat.{u}) (H : Over S)
  (e : (F ⋙ forget RingCat).RepresentableBy H)
  {R : Type u} [Ring R] {d : ℕ} (b : Basis (Fin d) ℤ R)

abbrev parameters : Over S := ∏ᶜ fun _ : Fin d => H

def values {T : Over S} (f : T ⟶ parameters (d := d) H) (i : Fin d) : F.obj (op T) :=
  e.homEquiv (f ≫ Pi.π (fun _ : Fin d => H) i)

def universalValues (i : Fin d) : F.obj (op (parameters (d := d) H)) :=
  e.homEquiv (Pi.π (fun _ : Fin d => H) i)

theorem values_eq_map {T : Over S} (f : T ⟶ parameters (d := d) H) (i : Fin d) :
    values F H e f i = (F.map f.op).hom (universalValues F H e i) :=
  e.homEquiv_comp f _

theorem classify_element {T : Over S} (f : T ⟶ parameters (d := d) H)
    (x : F.obj (op (parameters (d := d) H))) :
    e.homEquiv (f ≫ e.homEquiv.symm x) = (F.map f.op).hom x := by
  rw [e.homEquiv_comp, e.homEquiv.apply_symm_apply]
  rfl

def valuesEquiv (T : Over S) :
    (T ⟶ parameters (d := d) H) ≃ (Fin d → F.obj (op T)) where
  toFun := values F H e
  invFun v := Pi.lift (fun i => e.homEquiv.symm (v i))
  left_inv f := by
    apply Pi.hom_ext
    intro i
    rw [Pi.lift_comp_π]
    exact e.homEquiv.symm_apply_apply _
  right_inv v := by
    funext i
    change e.homEquiv (Pi.lift (fun j => e.homEquiv.symm (v j)) ≫ Pi.π _ i) = v i
    rw [Pi.lift_comp_π, e.homEquiv.apply_symm_apply]

theorem values_comp {T U : Over S} (f : T ⟶ U) (h : U ⟶ parameters (d := d) H)
    (i : Fin d) :
    values F H e (f ≫ h) i = (F.map f.op).hom (values F H e h i) := by
  change e.homEquiv ((f ≫ h) ≫ Pi.π _ i) = _
  rw [Category.assoc, e.homEquiv_comp]
  rfl

variable [IsSeparated H.hom]

def unitEquation : HilbertScheme.Presentations.EquationLoci.MorphismEquation (parameters (d := d) H) where
  target := H
  separated := inferInstance
  lhs := e.homEquiv.symm (Actions.basisExtension b (universalValues F H e) 1)
  rhs := e.homEquiv.symm 1

def multiplicationEquation (i j : Fin d) : HilbertScheme.Presentations.EquationLoci.MorphismEquation (parameters (d := d) H) where
  target := H
  separated := inferInstance
  lhs := e.homEquiv.symm (Actions.basisExtension b (universalValues F H e) (b i * b j))
  rhs := e.homEquiv.symm (universalValues F H e i * universalValues F H e j)

def equations : List (HilbertScheme.Presentations.EquationLoci.MorphismEquation (parameters (d := d) H)) :=
  unitEquation F H e b :: (List.ofFn fun i : Fin d =>
    List.ofFn fun j : Fin d => multiplicationEquation F H e b i j).flatten

def TableCondition {T : Over S} (f : T ⟶ parameters (d := d) H) : Prop :=
  Actions.basisExtension b (values F H e f) 1 = 1 ∧
    ∀ i j, Actions.basisExtension b (values F H e f) (b i * b j) =
      values F H e f i * values F H e f j

theorem equation_unit_iff {T : Over S} (f : T ⟶ parameters (d := d) H) :
    f ≫ (unitEquation F H e b).lhs = f ≫ (unitEquation F H e b).rhs ↔
      Actions.basisExtension b (values F H e f) 1 = 1 := by
  let c : (T ⟶ H) ≃ F.obj (op T) := e.homEquiv
  refine Iff.trans c.injective.eq_iff.symm ?_
  change e.homEquiv (f ≫ e.homEquiv.symm _) = e.homEquiv (f ≫ e.homEquiv.symm _) ↔ _
  rw [classify_element, classify_element, (F.map f.op).hom.map_one, basisExtension_map]
  rw [show values F H e f = fun i => (F.map f.op).hom (universalValues F H e i) from
    funext (values_eq_map F H e f)]

theorem equation_multiplication_iff {T : Over S} (f : T ⟶ parameters (d := d) H)
    (i j : Fin d) :
    f ≫ (multiplicationEquation F H e b i j).lhs =
        f ≫ (multiplicationEquation F H e b i j).rhs ↔
      Actions.basisExtension b (values F H e f) (b i * b j) =
        values F H e f i * values F H e f j := by
  let c : (T ⟶ H) ≃ F.obj (op T) := e.homEquiv
  refine Iff.trans c.injective.eq_iff.symm ?_
  change e.homEquiv (f ≫ e.homEquiv.symm _) = e.homEquiv (f ≫ e.homEquiv.symm _) ↔ _
  rw [classify_element, classify_element, (F.map f.op).hom.map_mul, basisExtension_map]
  rw [show values F H e f = fun i => (F.map f.op).hom (universalValues F H e i) from
    funext (values_eq_map F H e f)]

/-- The finite scheme equations express the full ring law, through the
proved finite-basis extension. -/
theorem satisfies_iff {T : Over S} (f : T ⟶ parameters (d := d) H) :
    HilbertScheme.Presentations.EquationLoci.Satisfies (equations F H e b) f ↔ TableCondition F H e b f := by
  constructor
  · intro hf
    refine ⟨(equation_unit_iff F H e b f).mp (hf _ List.mem_cons_self), ?_⟩
    intro i j
    apply (equation_multiplication_iff F H e b f i j).mp
    apply hf
    exact List.mem_cons_of_mem _ (List.mem_flatten.mpr
      ⟨List.ofFn fun k => multiplicationEquation F H e b i k,
        List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨j, rfl⟩⟩)
  · rintro ⟨hunit, hmul⟩ q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (equation_unit_iff F H e b f).mpr hunit
    · obtain ⟨qs, hqs, hq⟩ := List.mem_flatten.mp hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hqs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      exact (equation_multiplication_iff F H e b f i j).mpr (hmul i j)

/-- The actual finite equation locus uniquely classifies ring maps on
every test scheme through their values on the integral basis. -/
theorem exists_closed_action_locus :
    ∃ (Z : Over S) (j : Z ⟶ parameters (d := d) H), IsClosedImmersion j.left ∧
      TableCondition F H e b j ∧
      ∀ (T : Over S) (ρ : R →+* F.obj (op T)),
        ∃! f : T ⟶ Z, ∀ i, values F H e (f ≫ j) i = ρ (b i) := by
  obtain ⟨Z, j, hj, hZ⟩ := HilbertScheme.Presentations.EquationLoci.finite_equations_closed_locus (equations F H e b)
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  have hjTable : TableCondition F H e b j := (satisfies_iff F H e b j).mp
    ((hZ Z j).mpr ⟨𝟙 Z, Category.id_comp j, fun f hf =>
      (cancel_mono j).mp (hf.trans (Category.id_comp j).symm)⟩)
  refine ⟨Z, j, hj, hjTable, ?_⟩
  intro T ρ
  let p := (valuesEquiv F H e T).symm (fun i => ρ (b i))
  have hp : values F H e p = fun i => ρ (b i) := (valuesEquiv F H e T).apply_symm_apply _
  have hL : Actions.basisExtension b (fun i => ρ (b i)) = ρ.toAddMonoidHom.toIntLinearMap :=
    b.ext fun i => Actions.basisExtension_basis _ _ i
  have hpTable : TableCondition F H e b p := by
    change Actions.basisExtension b (values F H e p) 1 = 1 ∧ _
    rw [hp, hL]
    exact ⟨ρ.map_one, fun i j => ρ.map_mul (b i) (b j)⟩
  obtain ⟨f, hf, huniq⟩ := (hZ T p).mp ((satisfies_iff F H e b p).mpr hpTable)
  refine ⟨f, ?_, ?_⟩
  · intro i
    rw [hf]
    exact congrFun hp i
  · intro g hg
    apply huniq
    exact (valuesEquiv F H e T).injective ((funext hg).trans hp.symm)

/-- Construct the universal ring action on the closed locus and its
all-test-scheme classifying property in the ring-valued functor itself. -/
theorem exists_universal_action_scheme :
    ∃ (Z : Over S) (j : Z ⟶ parameters (d := d) H), IsClosedImmersion j.left ∧
      ∃ ρZ : R →+* F.obj (op Z),
        (∀ i, ρZ (b i) = values F H e j i) ∧
        ∀ (T : Over S) (ρ : R →+* F.obj (op T)),
          ∃! f : T ⟶ Z, (F.map f.op).hom.comp ρZ = ρ := by
  obtain ⟨Z, j, hj, htable, hclass⟩ := exists_closed_action_locus F H e b
  let ρZ := Actions.ringHomOfBasis b (values F H e j) htable.1 htable.2
  have hρZ (i) : ρZ (b i) = values F H e j i := Actions.ringHomOfBasis_basis _ _ _ _ i
  refine ⟨Z, j, hj, ρZ, hρZ, ?_⟩
  intro T ρ
  have iff_basis (f : T ⟶ Z) : (F.map f.op).hom.comp ρZ = ρ ↔
      ∀ i, values F H e (f ≫ j) i = ρ (b i) := by
    constructor
    · intro hf i
      have h := RingHom.congr_fun hf (b i)
      simpa only [RingHom.comp_apply, hρZ, ← values_comp] using h
    · intro hf
      have h : ((F.map f.op).hom.comp ρZ).toAddMonoidHom.toIntLinearMap =
          ρ.toAddMonoidHom.toIntLinearMap := b.ext fun i => by
        change (F.map f.op).hom (ρZ (b i)) = ρ (b i)
        rw [hρZ, ← values_comp]
        exact hf i
      exact RingHom.ext fun x => LinearMap.congr_fun h x
  obtain ⟨f, hf, huniq⟩ := hclass T ρ
  exact ⟨f, (iff_basis f).mpr hf, fun g hg => huniq g ((iff_basis g).mp hg)⟩

end FiniteActionLocus

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ActionLoci
