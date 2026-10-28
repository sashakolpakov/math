import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruentMaps

/-! # Reduced Center Pointed Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReducedCenterPointedDescent.Construction

noncomputable section

/-! Actual reduced centers descend from pointed comparisons, including their full ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem idealSheaf_radical_eq_of_reduced_subscheme {X : Scheme.{u}}
    (I : X.IdealSheafData) [IsReduced I.subscheme] : I.radical = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  change (I.ideal U).radical = I.ideal U
  rw [← I.ker_subschemeι_app U, RingHom.ker_eq_comap_bot, ← Ideal.comap_radical,
    Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot)]

theorem idealSheaf_eq_of_reduced_support_eq {X : Scheme.{u}}
    (I J : X.IdealSheafData) [IsReduced I.subscheme] [IsReduced J.subscheme]
    (h : I.support = J.support) : I = J := by
  have he := congrArg Scheme.IdealSheafData.vanishingIdeal h
  rwa [Scheme.IdealSheafData.vanishingIdeal_support, Scheme.IdealSheafData.vanishingIdeal_support,
    idealSheaf_radical_eq_of_reduced_subscheme, idealSheaf_radical_eq_of_reduced_subscheme] at he

theorem idealSheaf_eq_of_reduced_pointed_comap_eq {X : Scheme.{u}}
    (I J : X.IdealSheafData) [IsReduced I.subscheme] [IsReduced J.subscheme]
    (h : ∀ x : X, x ∈ I.support ∨ x ∈ J.support →
      ∃ (V : Scheme.{u}) (a : V ⟶ X) (y : V), a y = x ∧ I.comap a = J.comap a) : I = J := by
  apply idealSheaf_eq_of_reduced_support_eq
  ext x
  by_cases hx : x ∈ I.support ∨ x ∈ J.support
  · obtain ⟨V, a, y, hy, he⟩ := h x hx
    have hs := congrArg (fun L => y ∈ L.support) he
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at hs
    change (a y ∈ I.support) = (a y ∈ J.support) at hs
    rw [hy] at hs
    exact Iff.of_eq hs
  · exact ⟨fun hi => False.elim (hx (Or.inl hi)), fun hj => False.elim (hx (Or.inr hj))⟩

theorem idealSheaf_eq_of_reduced_tangent_comparisons {X : Scheme.{u}}
    (T I J : X.IdealSheafData) [IsReduced I.subscheme] [IsReduced J.subscheme]
    (hTI : T ≤ I) (hTJ : T ≤ J)
    (h : ∀ x : X, x ∈ T.support →
      ∃ (V : Scheme.{u}) (a b : V ⟶ X) (y : V), a y = x ∧
        IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent a b T ∧ I.comap a = J.comap b) : I = J := by
  apply idealSheaf_eq_of_reduced_pointed_comap_eq
  intro x hx
  have hxT : x ∈ T.support := hx.elim
    (fun hi => Scheme.IdealSheafData.support_antitone hTI hi)
    (fun hj => Scheme.IdealSheafData.support_antitone hTJ hj)
  obtain ⟨V, a, b, y, hy, hc, he⟩ := h x hxT
  exact ⟨V, a, y, hy, he.trans (hc.preservesIdeal J hTJ).symm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReducedCenterPointedDescent.Construction
