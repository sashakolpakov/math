import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Rational Order Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions

noncomputable section

/-! Actual open-immersion pullback preserves rational-function orders,
including negative orders, by stalk and quotient-length isomorphisms. -/

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

theorem ringOrderMonoid_equiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S] (e : R ≃+* S) (a : R) :
    Ring.ordMonoidWithZeroHom S (e a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · subst a
    simp only [map_zero]
  have ha' : e a ≠ 0 := (map_ne_zero_iff _ e.injective).mpr ha
  have hR : Ring.ord R a = ((Ring.ord R a).toNat : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm
  have hS := (ringOrder_equiv e a).trans hR
  rw [Ring.ordMonoidWithZeroHom_eq_coe S (mem_nonZeroDivisors_of_ne_zero ha') hS,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero ha) hR]

/-- Actual compatible ring and fraction-field isomorphisms preserve fraction orders. -/
theorem ringOrderFrac_equiv {R S K L : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (e : R ≃+* S) (φ : K ≃+* L)
    (hφ : ∀ a : R, φ (algebraMap R K a) = algebraMap S L (e a)) (f : K) :
    Ring.ordFrac S (φ f) = Ring.ordFrac R f := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [map_div₀, hφ a, hφ b, map_div₀, map_div₀,
    Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb',
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ e.injective).mpr ha),
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ e.injective).mpr hb'),
    ringOrderMonoid_equiv e a, ringOrderMonoid_equiv e b]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual pullback on generic stalks. -/
def genericFieldMap (i : X ⟶ Y) (hη : i (genericPoint X) = genericPoint Y) :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫ i.stalkMap (genericPoint X)

/-- Generic-stalk pullback commutes with the actual map from every local ring. -/
theorem genericFieldMap_stalk (i : X ⟶ Y)
    (hη : i (genericPoint X) = genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (i x)) :
    genericFieldMap i hη (algebraMap (Y.presheaf.stalk (i x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (i.stalkMap x a) := by
  have h : CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (i x)) Y.functionField) ≫
      genericFieldMap i hη = i.stalkMap x ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      genericFieldMap i hη = i.stalkMap x ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
    rw [genericFieldMap, TopCat.Presheaf.stalkCongr_hom,
      ← Category.assoc]
    exact (congrArg (fun k => k ≫ i.stalkMap (genericPoint X))
      (Y.presheaf.stalkSpecializes_comp (Inseparable.of_eq hη).specializes
        ((genericPoint_spec Y).specializes (Set.mem_univ (i x))))).trans
      (i.stalkSpecializes_stalkMap (genericPoint X) x
        ((genericPoint_spec X).specializes (Set.mem_univ x)))
  exact congrArg (fun k : Y.presheaf.stalk (i x) ⟶ X.functionField => k a) h

variable (i : X ⟶ Y) [IsOpenImmersion i]

def openFunctionFieldMap : Y.functionField ⟶ X.functionField :=
  genericFieldMap i (genericPoint_eq_of_isOpenImmersion i)

instance openFunctionFieldMap_isIso : IsIso (openFunctionFieldMap i) := by
  unfold openFunctionFieldMap genericFieldMap
  infer_instance

def openFunctionFieldIso : Y.functionField ≅ X.functionField := asIso (openFunctionFieldMap i)

theorem ord_openImmersion [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y.functionField) (x : X) :
    X.ord (openFunctionFieldMap i f) x = Y.ord f (i x) := by
  have hc : coheight (i x) = coheight x := coheight_eq_of_isOpenImmersion i
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 (Y.presheaf.stalk (i x)) := krullDimLE_of_coheight_le (hc.trans hx).le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx,
      Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg WithZero.log (ringOrderFrac_equiv
      (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
      (openFunctionFieldIso i).commRingCatIsoToRingEquiv
      (genericFieldMap_stalk i (genericPoint_eq_of_isOpenImmersion i) x) f)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions
