import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Divisor Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: restriction of effective Cartier divisor coefficients

Local quotient length is invariant under the actual stalk isomorphism of
an open immersion. Consequently the finite divisor of a nonzero global
function restricts coefficientwise to the divisor of its restriction.
This supplies the locality of the multiplicities used in specialization.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

universe u v

/-- Ring isomorphisms preserve the length defining the order of a regular function. -/
theorem ringOrder_equiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let eA : R ≃ₐ[R] S := { e with commutes' := fun _ => rfl }
  have hI : Ideal.span {e a} = (Ideal.span {a}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eQ := Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) eA hI
  exact (Module.length_eq_of_surjective (R := S) (M := S ⧸ Ideal.span {e a})
    e.surjective).symm.trans eQ.toLinearEquiv.length_eq.symm

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsOpenImmersion f]

/-- A nonzero global section remains nonzero on a nonempty integral open subscheme. -/
theorem openImmersion_appTop_ne_zero (a : Γ(Y, ⊤)) (ha : a ≠ 0) : f.appTop a ≠ 0 := by
  intro h
  let x : X := genericPoint X
  have hg : Y.presheaf.germ ⊤ (f x) (by trivial) a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral Y (f x) (by trivial))).mpr ha
  apply hg
  apply (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.injective
  change f.stalkMap x (Y.presheaf.germ ⊤ (f x) (by trivial) a) = f.stalkMap x 0
  have he := f.germ_stalkMap_apply ⊤ x (by trivial) a
  change f.stalkMap x (Y.presheaf.germ ⊤ (f x) (by trivial) a) =
    X.presheaf.germ ⊤ x (by trivial) (f.appTop a) at he
  exact he.trans ((congrArg (X.presheaf.germ ⊤ x (by trivial)) h).trans
    ((map_zero (X.presheaf.germ ⊤ x (by trivial)).hom).trans
      (map_zero (f.stalkMap x).hom).symm))

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

/-- The actual local-length divisor coefficients commute with open restriction. -/
theorem regularFunctionDivisor_openImmersion (a : Γ(Y, ⊤)) (ha : a ≠ 0) (x : X) :
    RegularDivisor.BundleCycles.regularFunctionDivisor X (f.appTop a) x = RegularDivisor.BundleCycles.regularFunctionDivisor Y a (f x) := by
  have hc : coheight (f x) = coheight x := coheight_eq_of_isOpenImmersion f
  by_cases hx : coheight x = 1
  · rw [RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length X _ (openImmersion_appTop_ne_zero f a ha) x hx,
      RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length Y a ha (f x) (hc.trans hx)]
    let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    have he : e (Y.presheaf.germ ⊤ (f x) (by trivial) a) =
        X.presheaf.germ ⊤ x (by trivial) (f.appTop a) :=
      f.germ_stalkMap_apply ⊤ x (by trivial) a
    have hl := ringOrder_equiv e (Y.presheaf.germ ⊤ (f x) (by trivial) a)
    rw [he] at hl
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hl
  · change X.ord (RegularDivisor.BundleCycles.globalFunctionFieldElement X (f.appTop a)) x =
      Y.ord (RegularDivisor.BundleCycles.globalFunctionFieldElement Y a) (f x)
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

/-- The finite divisor on the open subscheme is exactly coefficient restriction,
with no change to multiplicities. -/
theorem regularFunctionDivisor_comap (a : Γ(Y, ⊤)) (ha : a ≠ 0) :
    Finsupp.comapDomain f (RegularDivisor.BundleCycles.regularFunctionDivisor Y a) f.isOpenEmbedding.injective.injOn =
      RegularDivisor.BundleCycles.regularFunctionDivisor X (f.appTop a) := by
  ext x
  exact (regularFunctionDivisor_openImmersion f a ha x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction.BundleCycles
