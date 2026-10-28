import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedImmersionRegularity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartRefinement

/-! # Regular Subopen -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopen

noncomputable section

/-! Regular equations for a smooth closed center live on actual affine
subopens of the original scheme, with its original ideal sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u v

theorem regular_map {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) (rs : List A) (h : RingTheory.Sequence.IsRegular A rs) :
    RingTheory.Sequence.IsRegular B (rs.map e) := by
  apply (e.toAddEquiv.isRegular_congr
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun r _ x => ?_)))).mp h
  exact e.map_mul r x

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) (hU : IsAffineOpen U)
  {k : Type u} [CommRing k] [Algebra k Γ(X, U)] [IsNoetherianRing Γ(X, U)]
  [Algebra.Smooth k Γ(X, U)] [Algebra.Smooth k (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩)]

include k in
theorem exists_regular_subopen (p : PrimeSpectrum Γ(X, U))
    (hp : I.ideal ⟨U, hU⟩ ≤ p.asIdeal) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V), V ≤ U ∧ hU.fromSpec p ∈ V ∧
      ∃ rs : List Γ(X, V), I.ideal ⟨V, hV⟩ = Ideal.ofList rs ∧
        RingTheory.Sequence.IsRegular Γ(X, V) rs := by
  obtain ⟨S, hSk, hSs, φ, hφ, q, hq, r, z, D, hD, hI, hr⟩ :=
    ClosedImmersionRegularity.exists_pointed_open_regular_sequence
      (k := k) (I.ideal ⟨U, hU⟩) p hp
  let := hSk
  let := hSs
  let := hφ
  let V := Affine.ChartRefinement.openSet U hU φ.toRingHom
  let hV : IsAffineOpen V := Affine.ChartRefinement.affine U hU φ.toRingHom
  let e : Γ(X, V) ≃+* S :=
    (Affine.ChartRefinement.sectionsIso U hU φ.toRingHom).commRingCatIsoToRingEquiv
  refine ⟨V, hV, Affine.ChartRefinement.le U hU φ.toRingHom, ?_,
    (List.ofFn z).map e.symm, ?_, regular_map e.symm (List.ofFn z) hr⟩
  · refine ⟨q, trivial, ?_⟩
    change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ.toRingHom)) q) = hU.fromSpec p
    exact congrArg hU.fromSpec hq
  · have he : (I.ideal ⟨V, hV⟩).map e.toRingHom = Ideal.ofList (List.ofFn z) :=
      (Affine.ChartRefinement.ideal U hU φ.toRingHom I).trans hI
    have hb := congrArg (fun J : Ideal S => J.map e.symm.toRingHom) he
    simpa [Ideal.map_map] using hb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopen
