import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Forms Equivalence D -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence

noncomputable section

/-!
# Cohomology: identifying differential symbols with exterior Kähler forms

The universal property of Kähler differentials extends maps satisfying the
Leibniz rule in every argument to multilinear maps on the differential module.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable {M : Type u} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

omit [Module R M] [IsScalarTower R A M] in
/-- Multilinear maps on Kähler differentials are determined by tuples of exact forms. -/
theorem multilinear_ext_D (n : ℕ)
    (f g : MultilinearMap A (fun _ : Fin n => Ω[A⁄R]) M)
    (h : ∀ v : Fin n → A,
      f (fun i => KaehlerDifferential.D R A (v i)) =
        g (fun i => KaehlerDifferential.D R A (v i))) : f = g := by
  induction n with
  | zero =>
    ext v
    have hv : v = (fun i : Fin 0 => KaehlerDifferential.D R A ((fun i => i.elim0) i)) :=
      funext fun i => i.elim0
    rw [hv]
    exact h _
  | succ n ih =>
    apply (multilinearCurryLeftEquiv A (fun _ : Fin (n + 1) => Ω[A⁄R]) M).injective
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
    intro a
    apply ih
    intro v
    have heq : (fun i : Fin (n + 1) =>
        KaehlerDifferential.D R A ((Fin.cons a v : Fin (n + 1) → A) i)) =
        Fin.cons (KaehlerDifferential.D R A a) (fun i => KaehlerDifferential.D R A (v i)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    change f (Fin.cons (KaehlerDifferential.D R A a)
      (fun i => KaehlerDifferential.D R A (v i))) =
      g (Fin.cons (KaehlerDifferential.D R A a) (fun i => KaehlerDifferential.D R A (v i)))
    simpa only [heq] using h (Fin.cons a v)

/-- A map linear over the base ring and satisfying Leibniz in each argument
extends to a multilinear map on Kähler differentials. -/
theorem exists_multilinear_lift (n : ℕ)
    (f : MultilinearMap R (fun _ : Fin n => A) M)
    (hmul : ∀ (v : Fin n → A) (i : Fin n) (a b : A),
      f (Function.update v i (a * b)) =
        a • f (Function.update v i b) + b • f (Function.update v i a)) :
    ∃ g : MultilinearMap A (fun _ : Fin n => Ω[A⁄R]) M,
      ∀ v : Fin n → A, g (fun i => KaehlerDifferential.D R A (v i)) = f v := by
  induction n with
  | zero =>
    refine ⟨MultilinearMap.constOfIsEmpty A _ (f (fun i => i.elim0)), ?_⟩
    intro v
    change f (fun i : Fin 0 => i.elim0) = f v
    congr 1
    exact funext fun i => i.elim0
  | succ n ih =>
    have ht (a : A) : ∃ g : MultilinearMap A (fun _ : Fin n => Ω[A⁄R]) M,
        ∀ v : Fin n → A, g (fun i => KaehlerDifferential.D R A (v i)) =
          f (Fin.cons a v) := by
      apply ih (f.curryLeft a)
      intro v i x y
      simpa only [MultilinearMap.curryLeft_apply, Fin.cons_update] using
        hmul (Fin.cons a v) i.succ x y
    choose g hg using ht
    let : IsScalarTower R A (MultilinearMap A (fun _ : Fin n => Ω[A⁄R]) M) :=
      ⟨fun r a q => MultilinearMap.ext fun v => smul_assoc r a (q v)⟩
    let D : Derivation R A (MultilinearMap A (fun _ : Fin n => Ω[A⁄R]) M) :=
      { toFun := g
        map_add' := by
          intro a b
          apply multilinear_ext_D R A n
          intro v
          simp only [_root_.add_apply, hg, MultilinearMap.cons_add]
        map_smul' := by
          intro r a
          apply multilinear_ext_D R A n
          intro v
          simp only [_root_.smul_apply, hg, MultilinearMap.cons_smul, RingHom.id_apply]
        map_one_eq_zero' := by
          apply multilinear_ext_D R A n
          intro v
          change g 1 (fun i => KaehlerDifferential.D R A (v i)) = 0
          rw [hg]
          have h := hmul (Fin.cons 0 v) 0 1 1
          simp only [one_mul, one_smul, Fin.update_cons_zero] at h
          exact (add_left_cancel ((add_zero _).trans h)).symm
        leibniz' := by
          intro a b
          apply multilinear_ext_D R A n
          intro v
          change g (a * b) (fun i => KaehlerDifferential.D R A (v i)) =
            a • g b (fun i => KaehlerDifferential.D R A (v i)) +
              b • g a (fun i => KaehlerDifferential.D R A (v i))
          simp only [hg]
          simpa using hmul (Fin.cons 0 v) 0 a b }
    refine ⟨D.liftKaehlerDifferential.uncurryLeft, ?_⟩
    intro v
    simp only [LinearMap.uncurryLeft_apply, Derivation.liftKaehlerDifferential_comp_D]
    change g (v 0) (fun i => KaehlerDifferential.D R A (v i.succ)) = f v
    rw [hg]
    congr 1
    exact Fin.cons_self_tail v

/-- Extend the universal differential symbol in every argument. -/
def liftedSymbols (n : ℕ) :
    MultilinearMap A (fun _ : Fin n => Ω[A⁄R]) (DeRhamPresentationTo.DeRhamPresentation.Form R A n) :=
  Classical.choose (exists_multilinear_lift R A n (DeRhamPresentationTo.DeRhamPresentation.symbols R A n).toMultilinearMap
    (DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul R A))

@[simp]
theorem liftedSymbols_D (n : ℕ) (v : Fin n → A) :
    liftedSymbols R A n (fun i => KaehlerDifferential.D R A (v i)) = DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 v :=
  Classical.choose_spec (exists_multilinear_lift R A n (DeRhamPresentationTo.DeRhamPresentation.symbols R A n).toMultilinearMap
    (DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul R A)) v

theorem alternatization_liftedSymbols_D (n : ℕ) (v : Fin n → A) :
    MultilinearMap.alternatization (liftedSymbols R A n)
      (fun i => KaehlerDifferential.D R A (v i)) = n.factorial • DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 v := by
  have h := congrArg (fun a : AlternatingMap R A (DeRhamPresentationTo.DeRhamPresentation.Form R A n) (Fin n) => a v)
    (AlternatingMap.coe_alternatization (DeRhamPresentationTo.DeRhamPresentation.symbols R A n))
  simpa only [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    Function.comp_def, liftedSymbols_D, AlternatingMap.smul_apply, Fintype.card_fin,
    AlternatingMap.coe_multilinearMap, DeRhamPresentationTo.DeRhamPresentation.symbols_apply] using h

section Rational

variable [Algebra ℚ A]

/-- Alternation normalized by the factorial, over a rational algebra. -/
def normalizedSymbols (n : ℕ) : AlternatingMap A Ω[A⁄R] (DeRhamPresentationTo.DeRhamPresentation.Form R A n) (Fin n) :=
  algebraMap ℚ A ((n.factorial : ℚ)⁻¹) •
    MultilinearMap.alternatization (liftedSymbols R A n)

@[simp]
theorem normalizedSymbols_D (n : ℕ) (v : Fin n → A) :
    normalizedSymbols R A n (fun i => KaehlerDifferential.D R A (v i)) =
      DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 v := by
  rw [normalizedSymbols, AlternatingMap.smul_apply, alternatization_liftedSymbols_D,
    ← Nat.cast_smul_eq_nsmul A, smul_smul]
  have h : algebraMap ℚ A ((n.factorial : ℚ)⁻¹) * (n.factorial : A) = 1 := by
    rw [← map_natCast (algebraMap ℚ A), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), map_one]
  rw [h, one_smul]

/-- The inverse interpretation of exterior Kähler forms as differential symbols. -/
def fromExterior (n : ℕ) : ⋀[A]^n Ω[A⁄R] →ₗ[A] DeRhamPresentationTo.DeRhamPresentation.Form R A n :=
  exteriorPower.alternatingMapLinearEquiv (normalizedSymbols R A n)

@[simp]
theorem fromExterior_exteriorSymbol (n : ℕ) (v : Fin n → A) :
    fromExterior R A n (DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol R A n v) = DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 v := by
  exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans
    (normalizedSymbols_D R A n v)

theorem fromExterior_toExterior (n : ℕ) (ω : DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    fromExterior R A n (DeRhamPresentationTo.DeRhamPresentation.toExterior R A n ω) = ω := by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single v a =>
    change fromExterior R A n (DeRhamPresentationTo.DeRhamPresentation.toExterior R A n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = DeRhamPresentationTo.DeRhamPresentation.symbol R A a v
    rw [DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol, map_smul, fromExterior_exteriorSymbol, ← DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

/-- In characteristic zero the explicit presentation is canonically equivalent
to the usual exterior power of Kähler differentials. -/
def formsEquiv (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[A] ⋀[A]^n Ω[A⁄R] :=
  LinearEquiv.ofBijective (DeRhamPresentationTo.DeRhamPresentation.toExterior R A n)
    ⟨Function.LeftInverse.injective (fromExterior_toExterior R A n),
      DeRhamPresentationTo.DeRhamPresentation.toExterior_surjective R A n⟩

@[simp]
theorem formsEquiv_symbol (n : ℕ) (a : A) (v : Fin n → A) :
    formsEquiv R A n (DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a • DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol R A n v :=
  DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol R A a v

end Rational

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R}

/-- The interpretation of forms commutes with algebra homomorphisms. -/
theorem toExterior_natural {B C : CommAlgCat.{u} R} (f : B ⟶ C) (n : ℕ)
    (ω : DeRhamPresentationTo.DeRhamPresentation.Form R B n) :
    DeRhamPresentationTo.DeRhamPresentation.toExterior R C n (DeRhamGlobalId.DeRhamGlobal.formMap f n ω) =
      AlgebraicForms.AlgebraicDeRham.formsMap f n (DeRhamPresentationTo.DeRhamPresentation.toExterior R B n ω) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R B n) ω
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v a =>
    change DeRhamPresentationTo.DeRhamPresentation.toExterior R C n (DeRhamGlobalId.DeRhamGlobal.formMap f n (DeRhamPresentationTo.DeRhamPresentation.symbol R B a v)) =
      AlgebraicForms.AlgebraicDeRham.formsMap f n (DeRhamPresentationTo.DeRhamPresentation.toExterior R B n (DeRhamPresentationTo.DeRhamPresentation.symbol R B a v))
    simp only [DeRhamGlobalId.DeRhamGlobal.formMap_symbol, DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol,
      AlgebraicForms.AlgebraicDeRham.formsMap_smul, DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol, AlgebraicForms.AlgebraicDeRham.formsMap_mk,
      AlgebraicForms.AlgebraicDeRham.oneFormsMap_D]

variable (R) [Algebra ℚ R]

/-- The form equivalence on each coordinate algebra, with scalars restricted
to the base ring. -/
def coordinateFormsEquiv (B : CommAlgCat.{u} R) (n : ℕ) :
    DeRhamPresentationTo.DeRhamPresentation.Form R B n ≃ₗ[R] AlgebraicForms.AlgebraicDeRham.Forms B n := by
  let : Algebra ℚ B := Algebra.compHom B (algebraMap ℚ R)
  exact (formsEquiv R B n).restrictScalars R

/-- A natural isomorphism from the symbol presentation to exterior forms. -/
def formsFunctorIso (n : ℕ) :
    DeRhamGlobalId.DeRhamGlobal.formsFunctor (R := R) n ≅ AlgebraicForms.AlgebraicDeRham.formsFunctor (R := R) n :=
  NatIso.ofComponents
    (fun B => (coordinateFormsEquiv R B n).toModuleIso)
    (fun f => ModuleCat.hom_ext (LinearMap.ext (fun ω => toExterior_natural f n ω)))

/-- The identification commutes with all restrictions on the scheme. -/
def formsPresheafIso (X : Over (Spec (CommRingCat.of R))) (n : ℕ) :
    DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n ≅ AlgebraicForms.AlgebraicDeRham.formsPresheaf R X n :=
  (Functor.whiskeringLeft _ _ _).obj (AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X) |>.mapIso
    (formsFunctorIso R n)

/-- After sheafification, the global complex has the usual exterior form
sheaf in every degree. -/
def formsSheafIso (X : Over (Spec (CommRingCat.of R))) (n : ℕ) :
    (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n ≅ AlgebraicForms.AlgebraicDeRham.formsSheaf R X n :=
  (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)).mapIso
    (formsPresheafIso R X n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence
