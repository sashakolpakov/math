import OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.FactorTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComponentBoundaryAtlas

/-! # Controlled Comaximal Products -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ControlledComaximalProducts.Construction

noncomputable section

/-! Controlled transforms preserve products of pairwise comaximal boundary factors without a permissibility assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ideal_colon_comaximal_product {R : Type*} [CommRing R]
    (A B C : Ideal R) (h : A ⊔ B = ⊤) :
    (A * B).colon (C : Set R) = A.colon (C : Set R) * B.colon (C : Set R) := by
  have hc : A.colon (C : Set R) ⊔ B.colon (C : Set R) = ⊤ := by
    apply top_le_iff.mp
    rw [← h]
    exact sup_le_sup Ideal.le_colon Ideal.le_colon
  rw [Ideal.mul_eq_inf_of_coprime h, Submodule.inf_colon, ← Ideal.mul_eq_inf_of_coprime hc]

theorem noetherianIdealSheafColon_comaximal_product
    {X : Scheme} [IsLocallyNoetherian X] (A B C : X.IdealSheafData) (h : A ⊔ B = ⊤) :
    NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (A * B) C = NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon A C * NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon B C := by
  apply Scheme.IdealSheafData.ext
  funext U
  exact ideal_colon_comaximal_product (A.ideal U) (B.ideal U) (C.ideal U)
    (congrArg (fun N => N.ideal U) h)

theorem globalBlowupControlledIdeal_comaximal_product
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I A B : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) (h : A ⊔ B = ⊤) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (A * B) hI b =
      GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I A hI b * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I B hI b := by
  have hs : A.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ⊔ B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_sup, h, Scheme.IdealSheafData.comap_top]
  unfold GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal GlobalControlled.Ideal.Construction.controlledIdealSheaf
  rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul, noetherianIdealSheafColon_comaximal_product _ _ _ hs]

theorem globalBlowupControlledIdeal_preserves_sup_top
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I A B : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) (h : A ⊔ B = ⊤) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I A hI b ⊔ GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I B hI b = ⊤ := by
  apply top_le_iff.mp
  have hs : A.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ⊔ B.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_sup, h, Scheme.IdealSheafData.comap_top]
  rw [← hs]
  exact sup_le_sup (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I A b _) (GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I B b _)

theorem globalBlowupControlledIdeal_finset_comaximal_product
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (b : ℕ) {β : Type}
    (D : β → X.IdealSheafData) (S : Finset β)
    (hD : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → D i ⊔ D j = ⊤) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (∏ j ∈ S, D j) hI b =
      ∏ j ∈ S, GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (D j) hI b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      apply Scheme.IdealSheafData.ext
      funext U
      change (((⊤ : X.IdealSheafData).comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)).ideal U).colon _ = ⊤
      rw [Scheme.IdealSheafData.comap_top]
      exact Submodule.top_colon
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        globalBlowupControlledIdeal_comaximal_product I (D i) (∏ j ∈ S, D j) hI b
          (Smooth.ComponentBoundaryAtlas.Construction.idealSheaf_sup_finset_prod_eq_top (D i) D S
            (fun j hj => hD i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
              (fun he => hi (he.symm ▸ hj)))),
        ih (fun i hi j hj hij => hD i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ControlledComaximalProducts.Construction
