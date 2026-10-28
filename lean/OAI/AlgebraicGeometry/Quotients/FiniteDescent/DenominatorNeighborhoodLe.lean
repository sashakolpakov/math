import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorStalkIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PrincipalNeighborhoodEq

/-! # Denominator Neighborhood Le -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorNeighborhoodLe.Construction.DenominatorNeighborhood

noncomputable section

/-! Principal affine neighborhoods for the denominator ideals of rational functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_principal {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [Smooth f]
    (r : X.functionField) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ ((DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U).IsPrincipal := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let p := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let I := (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal ⟨V, hV⟩
  have hp : (I.map (algebraMap Γ(X, V) (X.presheaf.stalk x))).IsPrincipal := by
    change (I.map (X.presheaf.germ V x hxV).hom).IsPrincipal
    rw [show I = (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal ⟨V, hV⟩ from rfl,
      DenominatorStalkIs.Construction.DenominatorStalk.map_stalk r ⟨V, hV⟩ ⟨x, hxV⟩]
    exact DenominatorStalkIs.Construction.DenominatorStalk.isPrincipal f r x
  obtain ⟨s, hsp, hs⟩ := PrincipalNeighborhoodEq.Construction.PrincipalTransport.exists_away_isPrincipal
    (A := X.presheaf.stalk x) I I.fg_of_isNoetherianRing p hp
  refine ⟨X.affineBasicOpen s, ?_, ?_⟩
  · apply (X.mem_basicOpen s x hxV).mpr
    change s ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal at hsp
    rw [hV.primeIdealOf_eq_map_closedPoint] at hsp
    change ¬ (X.presheaf.germ V x hxV) s ∈ IsLocalRing.maximalIdeal _ at hsp
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hsp
  · let : Algebra Γ(X, V) Γ(X, X.basicOpen s) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
    have := hV.isLocalization_basicOpen s
    rw [← (DenominatorSheafEq.Construction.DenominatorSheaf.data r).map_ideal_basicOpen ⟨V, hV⟩ s]
    change (I.map (algebraMap Γ(X, V) Γ(X, X.basicOpen s))).IsPrincipal
    exact PrincipalNeighborhoodEq.Construction.PrincipalTransport.map_algHom (R := Γ(X, V))
      (A := Localization.Away s) (B := Γ(X, X.basicOpen s)) I
      (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
        Γ(X, X.basicOpen s)).toAlgHom hs

theorem exists_principal_le {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of K)) [Smooth f]
    (r : X.functionField) (W : X.Opens) (x : W) :
    ∃ U : X.affineOpens, x.1 ∈ U.1 ∧ U.1 ≤ W ∧
      ((DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U).IsPrincipal := by
  obtain ⟨V, hxV, a, ha⟩ := exists_principal f r x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x.1 ∈ V.1 ⊓ W from ⟨hxV, x.2⟩) (V.1 ⊓ W).isOpen
  refine ⟨⟨U, hU⟩, hxU, fun y hy => (hUV hy).2, ?_⟩
  have hUV' : U ≤ V.1 := fun y hy => (hUV hy).1
  rw [← (DenominatorSheafEq.Construction.DenominatorSheaf.data r).map_ideal (show (⟨U, hU⟩ : X.affineOpens) ≤ V from hUV')]
  change (DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal V = Ideal.span {a} at ha
  rw [ha, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorNeighborhoodLe.Construction.DenominatorNeighborhood
