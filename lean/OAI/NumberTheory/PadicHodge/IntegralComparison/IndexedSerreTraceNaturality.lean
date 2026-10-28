import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedSerreUnitTrace

/-! # Indexed Serre Trace Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedSerreTraceNaturality

noncomputable section

/-! Reindexing complementary cohomology to degree zero preserves the
naturality of a Serre pairing and its unit-normalized trace. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R]
  (V₁ V₂ : ℕ → ModuleCat.{u} R) {A₁ A₂ : AddCommGrpCat.{u}} {n : ℕ}
  (p₁ : A₁ ≅ DualHomologyTransport.dualGroup R (V₁ n))
  (p₂ : A₂ ≅ DualHomologyTransport.dualGroup R (V₂ n))
  (hn : n = 0) (a : A₂ ⟶ A₁) (b : ∀ j, V₁ j ⟶ V₂ j)
  (h : a ≫ p₁.hom = p₂.hom ≫ DualTransportNaturality.dualMap R (b n))

include h

@[reassoc]
theorem pairing :
    a ≫ (IndexedSerreUnitTrace.pairing R V₁ p₁ hn).hom =
      (IndexedSerreUnitTrace.pairing R V₂ p₂ hn).hom ≫
        DualTransportNaturality.dualMap R (b 0) := by
  have hb : b n ≫ (eqToIso (congrArg V₂ hn)).hom =
      (eqToIso (congrArg V₁ hn)).hom ≫ b 0 := by
    subst n
    simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  exact DualTransportNaturality.transport_naturality R a (b n) (b 0)
    p₁ p₂ (eqToIso (congrArg V₁ hn)) (eqToIso (congrArg V₂ hn)) h hb

@[reassoc]
theorem trace (v₁ : V₁ 0) (v₂ : V₂ 0) (hv : b 0 v₁ = v₂) :
    a ≫ SerreUnitTrace.trace R (IndexedSerreUnitTrace.pairing R V₁ p₁ hn) v₁ =
      SerreUnitTrace.trace R (IndexedSerreUnitTrace.pairing R V₂ p₂ hn) v₂ :=
  SerreUnitTrace.naturality R _ _ a (b 0) v₁ v₂
    (pairing R V₁ V₂ p₁ p₂ hn a b h) hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedSerreTraceNaturality
