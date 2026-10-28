import OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedSerreUnitTrace

/-! # Indexed Concentration Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedConcentrationTrace

noncomputable section

/-! Concentrating a total duality class preserves its unit trace,
including the cast between the total degree and the sum of the two
cohomological degrees. -/

open _root_.CategoryTheory

universe u
variable (R : Type u) [CommRing R]
  (D : ℕ → AddCommGrpCat.{u}) (V : ℕ → ModuleCat.{u} R)
  (N i c : ℕ)
  (e : ∀ d, d ≤ N → (D d ≅ DualHomologyTransport.dualGroup R (V (N - d))))
  {T : AddCommGrpCat.{u}} (a : D (i + c) ≅ T) (hi : i + c = N)

theorem trace (v : V 0) :
    (eqToIso (congrArg D hi.symm) ≪≫ a).hom ≫
      SerreUnitTrace.trace R
        (IndexedSerreUnitTrace.pairing R V (a.symm ≪≫ e (i + c) hi.le)
          (by omega)) v =
    SerreUnitTrace.trace R
      (IndexedSerreUnitTrace.pairing R V (e N le_rfl) (Nat.sub_self N)) v := by
  subst N
  simp only [SerreUnitTrace.trace, IndexedSerreUnitTrace.pairing,
    DualHomologyTransport.transport, Iso.trans_hom, Iso.symm_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IndexedConcentrationTrace
