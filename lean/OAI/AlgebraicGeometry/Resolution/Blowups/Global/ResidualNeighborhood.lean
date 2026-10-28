import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderSequenceExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Companion

/-! # Residual Neighborhood -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood.Construction

/-! The terminal companion drop gives an actual lower-residual-order neighborhood of the entire remaining order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem idealSheaf_support_subset_complement_of_sup_top
    {X : Scheme} (I J : X.IdealSheafData) (h : I ⊔ J = ⊤) :
    (I.support : Set X) ⊆ J.support.compl := by
  intro x hx hj
  have hs : x ∈ (I ⊔ J).support := by
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨hx, hj⟩
  rw [h, Scheme.IdealSheafData.support_top] at hs
  exact hs

theorem idealSheaf_comap_supportComplement_eq_top {X : Scheme} (I : X.IdealSheafData) :
    I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  exact x.property hx

def residualOrderDropOpen {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (m : ℕ) : X.Opens :=
  (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1)).support.compl

theorem residualOrderDropOpen_residual_bound {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (m : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((residualOrderDropOpen f J m).ι ≫ f)
      (J.comap (residualOrderDropOpen f J m).ι) (m - 1) = ⊤ := by
  rw [← Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open]
  exact idealSheaf_comap_supportComplement_eq_top _

theorem residualOrderDropOpen_contains_order_support
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (M J : X.IdealSheafData) (m b : ℕ)
    (hd : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (M * J) (b - 1) ⊔
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) = ⊤) :
    ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (M * J) (b - 1)).support : Set X) ⊆
      Set.range (residualOrderDropOpen f J m).ι := by
  intro x hx
  exact ⟨⟨x, idealSheaf_support_subset_complement_of_sup_top _ _ hd hx⟩, rfl⟩

theorem exists_global_sequence_of_residual_order_neighborhood
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (M J : X.IdealSheafData) (m b : ℕ)
    (hMJ : M * J ≠ ⊥)
    (hd : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (M * J) (b - 1) ⊔
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) = ⊤)
    (T : MonomialSequence.Construction.SmoothFixedControlSequence b (residualOrderDropOpen f J m)
      ((residualOrderDropOpen f J m).ι ≫ f) ((M * J).comap (residualOrderDropOpen f J m).ι)) :
    Nonempty (MonomialSequence.Construction.SmoothFixedControlSequence b X f (M * J)) :=
  T.extend_from_order_neighborhood X f (M * J) hMJ (residualOrderDropOpen f J m).ι
    rfl rfl (residualOrderDropOpen_contains_order_support f M J m b hd)

end AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood.Construction

namespace AlgebraicGeometry.Resolution.Blowups.Global
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
section

/-! Continue a global companion phase using an actual sequence only on its lower-order residual neighborhood. -/

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.terminal_product_ne_bot {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {M J : X.IdealSheafData} (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J)
    (hmb : m ≤ b) (hMJ : M * J ≠ ⊥) : T.exceptionalIdeal * T.residualIdeal ≠ ⊥ := by
  induction T with
  | terminal => exact hMJ
  | @blowup Y hY hN g hg M J hbound I hI hM hJ hs hbl tail ih =>
      apply ih
      rw [← CompanionTransform.Construction.globalBlowup_companion_product_transform I M J hI m b hmb hM hJ]
      exact GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I (M * J) hI b hMJ

def CompanionSequence.Construction.SmoothGlobalCompanionSequence.residualNeighborhood {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {M J : X.IdealSheafData} (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : T.endpoint.Opens :=
  ResidualNeighborhood.Construction.residualOrderDropOpen (T.toBase ≫ f) T.residualIdeal m

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.residualNeighborhood_bound {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {M J : X.IdealSheafData} (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.residualNeighborhood.ι ≫ (T.toBase ≫ f))
      (T.residualIdeal.comap T.residualNeighborhood.ι) (m - 1) = ⊤ :=
  ResidualNeighborhood.Construction.residualOrderDropOpen_residual_bound (T.toBase ≫ f) T.residualIdeal m

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.attachControl_from_residualNeighborhood {m b : ℕ}
    {X : Scheme} [IsIntegral X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) (hb : 0 < b) (hmb : m ≤ b)
    (hMJ : M * J ≠ ⊥)
    (rest : MonomialSequence.Construction.SmoothFixedControlSequence b T.residualNeighborhood
      (T.residualNeighborhood.ι ≫ (T.toBase ≫ f))
      ((T.exceptionalIdeal * T.residualIdeal).comap T.residualNeighborhood.ι)) :
    Nonempty (MonomialSequence.Construction.SmoothFixedControlSequence b X f (M * J)) := by
  let : IsIntegral T.endpoint := T.endpoint_integral
  let : IsLocallyNoetherian T.endpoint := LocallyOfFiniteType.isLocallyNoetherian (T.toBase ≫ f)
  obtain ⟨U⟩ := ResidualNeighborhood.Construction.exists_global_sequence_of_residual_order_neighborhood
    (T.toBase ≫ f) T.exceptionalIdeal T.residualIdeal m b (T.terminal_product_ne_bot hmb hMJ)
    T.terminal_residual_drop rest
  exact ⟨T.attachControl hb hmb U⟩

end

/-! Nonempty integral residual neighborhoods and their native nonzero ideals. -/

theorem ResidualNeighborhood.Construction.residualOrderDropOpen_nonempty {X : Scheme} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥) (m : ℕ) :
    Nonempty (ResidualNeighborhood.Construction.residualOrderDropOpen f J m) := by
  by_contra h
  apply OrderCenterExtension.Construction.differential_order_support_ne_univ f J hJ (m - 1)
  apply Set.eq_univ_of_forall
  intro x
  by_contra hx
  exact h ⟨⟨x, hx⟩⟩

theorem ResidualNeighborhood.Construction.residualOrderDropOpen_integral {X : Scheme} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥) (m : ℕ) :
    IsIntegral (ResidualNeighborhood.Construction.residualOrderDropOpen f J m) := by
  let : Nonempty (ResidualNeighborhood.Construction.residualOrderDropOpen f J m) := ResidualNeighborhood.Construction.residualOrderDropOpen_nonempty f J hJ m
  exact isIntegral_of_isOpenImmersion (ResidualNeighborhood.Construction.residualOrderDropOpen f J m).ι

theorem ResidualNeighborhood.Construction.idealSheaf_right_factor_ne_bot {X : Scheme} (M J : X.IdealSheafData)
    (h : M * J ≠ ⊥) : J ≠ ⊥ := by
  intro hz
  apply h
  apply Scheme.IdealSheafData.ext
  funext U
  change (M.ideal U) * (J.ideal U) = ⊥
  rw [hz]
  exact Ideal.mul_bot (M.ideal U)

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.residualNeighborhood_integral
    {m b : ℕ} {X : Scheme} [IsIntegral X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) (hmb : m ≤ b) (hMJ : M * J ≠ ⊥) :
    IsIntegral T.residualNeighborhood := by
  let : IsIntegral T.endpoint := T.endpoint_integral
  exact ResidualNeighborhood.Construction.residualOrderDropOpen_integral (T.toBase ≫ f) T.residualIdeal
    (ResidualNeighborhood.Construction.idealSheaf_right_factor_ne_bot _ _ (T.terminal_product_ne_bot hmb hMJ)) m

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.residualNeighborhood_product_ne_bot
    {m b : ℕ} {X : Scheme} [IsIntegral X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) (hmb : m ≤ b) (hMJ : M * J ≠ ⊥) :
    (T.exceptionalIdeal * T.residualIdeal).comap T.residualNeighborhood.ι ≠ ⊥ := by
  let : IsIntegral T.endpoint := T.endpoint_integral
  let : IsIntegral T.residualNeighborhood := T.residualNeighborhood_integral hmb hMJ
  let : IsDominant T.residualNeighborhood.ι := by
    constructor
    exact T.residualNeighborhood.ι.opensRange.isOpen.dense
      (Set.range_nonempty T.residualNeighborhood.ι)
  let : IsSchemeTheoreticallyDominant T.residualNeighborhood.ι :=
    IsSchemeTheoreticallyDominant.of_isDominant T.residualNeighborhood.ι
  exact GlobalBlowup.Nonzero.Construction.idealSheaf_comap_ne_bot_of_ker_eq_bot T.residualNeighborhood.ι
    T.residualNeighborhood.ι.ker_eq_bot _ (T.terminal_product_ne_bot hmb hMJ)

end AlgebraicGeometry.Resolution.Blowups.Global

end

end OAI
