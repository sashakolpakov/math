import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.StabilizerLocalImage

/-! # Zero Set Local Orbit -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ZeroSetLocalOrbit.Construction

noncomputable section

section

/-! A family whose derivative spans a quadratic constraint's tangent
kernel fills a neighborhood of the zero set, provided it preserves that
constraint. This is the inverse-function step for bracket rigidity. -/

open scoped Classical _root_.Topology
open Filter Set

theorem quadratic_zero_set_local_orbit
    {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : V → Prop) (D : V →L[ℝ] F) (a : E →L[ℝ] V)
    (ha : Function.Injective a) (hrange : a.toLinearMap.range = D.toLinearMap.ker)
    (C : ℝ) (hC : 0 ≤ C) (hquad : ∀ x, R x → ‖D x‖ ≤ C * ‖x‖ ^ 2)
    (P : E × V → V) (hP0 : P 0 = 0)
    (hP : HasStrictFDerivAt P (a.coprod (ContinuousLinearMap.id ℝ V)) 0)
    (hR : ∀ p x, R (P (p, x)) → R x) :
    ∀ᶠ x in 𝓝 (0 : V), R x → x ∈ range (fun p => P (p, 0)) := by
  obtain ⟨W, hW⟩ := a.toLinearMap.range.exists_isCompl
  have hdisj : Disjoint W D.toLinearMap.ker := by
    rw [← hrange]
    exact hW.disjoint.symm
  obtain ⟨ε, hε, hisolated⟩ := Lie.AutomorphismTransversal.Construction.quadratic_remainder_isolated_on_complement
    D.toLinearMap W hdisj C hC
  let e : (E × W) ≃L[ℝ] V :=
    (((LinearEquiv.ofInjective a.toLinearMap ha).prodCongr (LinearEquiv.refl ℝ W)).trans
      (Submodule.prodEquivOfIsCompl _ W hW)).toContinuousLinearEquiv
  let j : (E × W) →L[ℝ] (E × V) :=
    (ContinuousLinearMap.fst ℝ E W).prod
      (W.subtypeL.comp (ContinuousLinearMap.snd ℝ E W))
  let Q : E × W → V := P ∘ j
  have hQ0 : Q 0 = 0 := by simp only [Q, Function.comp_apply, map_zero, hP0]
  have hQ : HasStrictFDerivAt Q (e : (E × W) →L[ℝ] V) 0 := by
    have hd := hP.comp (0 : E × W) j.hasStrictFDerivAt
    convert! hd using 1
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace V := FiniteDimensional.complete ℝ V
  let : CompleteSpace W := FiniteDimensional.complete ℝ W
  have hsmall : {p : E × W | ‖(p.2 : V)‖ < ε} ∈ 𝓝 0 := by
    have ho : IsOpen {p : E × W | ‖(p.2 : V)‖ < ε} :=
      isOpen_lt (continuous_subtype_val.comp continuous_snd).norm continuous_const
    exact ho.mem_nhds (by simpa using hε)
  have himage : Q '' {p : E × W | ‖(p.2 : V)‖ < ε} ∈ 𝓝 (0 : V) := by
    rw [← hQ0, ← hQ.map_nhds_eq_of_equiv (f' := e)]
    exact Filter.image_mem_map hsmall
  filter_upwards [himage] with x hx
  intro hRx
  obtain ⟨⟨p, q⟩, hq, rfl⟩ := hx
  have hqR : R (q : V) := hR p q hRx
  have hq0 : (q : V) = 0 := hisolated q q.property hq (hquad q hqR)
  refine ⟨p, ?_⟩
  change P (p, 0) = P (p, (q : V))
  rw [hq0]

end

/-! The local orbit criterion only requires that the derivative's
range equal the tangent kernel; redundant parameters can be removed. -/

open scoped _root_.Topology
open Filter Set

theorem quadratic_zero_set_local_orbit_of_range
    {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : V → Prop) (D : V →L[ℝ] F) (a : E →L[ℝ] V)
    (hrange : a.toLinearMap.range = D.toLinearMap.ker)
    (C : ℝ) (hC : 0 ≤ C) (hquad : ∀ x, R x → ‖D x‖ ≤ C * ‖x‖ ^ 2)
    (P : E × V → V) (hP0 : P 0 = 0)
    (hP : HasStrictFDerivAt P (a.coprod (ContinuousLinearMap.id ℝ V)) 0)
    (hR : ∀ p x, R (P (p, x)) → R x) :
    ∀ᶠ x in 𝓝 (0 : V), R x → x ∈ range (fun p => P (p, 0)) := by
  obtain ⟨W, hW⟩ := a.toLinearMap.ker.exists_isCompl
  let a' := a.comp W.subtypeL
  have hi : Function.Injective a' := by
    apply (injective_iff_map_eq_zero a').mpr
    intro x hx
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hW.disjoint x.val hx x.property
  have hr : a'.toLinearMap.range = a.toLinearMap.range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ a.toLinearMap.ker ⊔ W := by rw [hW.sup_eq_top]; trivial
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨v, hv⟩, ?_⟩
      change a v = a x
      rw [← huv, map_add, show a u = 0 from hu, zero_add]
  let j : W × V →L[ℝ] E × V :=
    (W.subtypeL.comp (ContinuousLinearMap.fst ℝ W V)).prod (ContinuousLinearMap.snd ℝ W V)
  have hd : HasStrictFDerivAt (P ∘ j) (a'.coprod (ContinuousLinearMap.id ℝ V)) 0 := by
    convert! hP.comp (0 : W × V) j.hasStrictFDerivAt using 1
  have h := quadratic_zero_set_local_orbit R D a' hi (hr.trans hrange) C hC hquad
    (P ∘ j) (by simpa only [Function.comp_apply, map_zero] using hP0) hd
    (fun p x => hR p.val x)
  filter_upwards [h] with x hx
  intro hRx
  obtain ⟨p, hp⟩ := hx hRx
  exact ⟨p.val, hp⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ZeroSetLocalOrbit.Construction
