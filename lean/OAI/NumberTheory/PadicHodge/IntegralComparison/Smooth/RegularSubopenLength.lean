import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequenceLength
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopen

/-! # Regular Subopen Length -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopenLength

noncomputable section

/-! The regular equations on actual affine subopens retain the
codimension computed at the original point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) (hU : IsAffineOpen U)
  {k : Type u} [CommRing k] [Algebra k Γ(X, U)] [IsNoetherianRing Γ(X, U)]
  [Algebra.Smooth k Γ(X, U)] [Algebra.Smooth k (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩)]

theorem exists_regular_subopen (p : PrimeSpectrum (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩)) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V), V ≤ U ∧
      hU.fromSpec (p.comap (Ideal.Quotient.mk (I.ideal ⟨U, hU⟩))) ∈ V ∧
      ∃ rs : List Γ(X, V), I.ideal ⟨V, hV⟩ = Ideal.ofList rs ∧
        RingTheory.Sequence.IsRegular Γ(X, V) rs ∧
        rs.length = Module.rankAtStalk Ω[Γ(X, U)⁄k]
            (p.comap (Ideal.Quotient.mk (I.ideal ⟨U, hU⟩))) -
          Module.rankAtStalk Ω[Γ(X, U) ⧸ I.ideal ⟨U, hU⟩⁄k] p := by
  obtain ⟨S, hSk, hSs, φ, hφ, q, hq, r, z, D, hD, hI, hr, hlen⟩ :=
    RegularSequenceLength.exists_pointed_open_regular_sequence
      (k := k) (I.ideal ⟨U, hU⟩) p
  let := hSk
  let := hSs
  let := hφ
  let V := Affine.ChartRefinement.openSet U hU φ.toRingHom
  let hV : IsAffineOpen V := Affine.ChartRefinement.affine U hU φ.toRingHom
  let e : Γ(X, V) ≃+* S :=
    (Affine.ChartRefinement.sectionsIso U hU φ.toRingHom).commRingCatIsoToRingEquiv
  refine ⟨V, hV, Affine.ChartRefinement.le U hU φ.toRingHom, ?_,
    (List.ofFn z).map e.symm, ?_,
    RegularSubopen.regular_map e.symm (List.ofFn z) hr, ?_⟩
  · refine ⟨q, trivial, ?_⟩
    change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ.toRingHom)) q) = _
    exact congrArg hU.fromSpec hq
  · have he : (I.ideal ⟨V, hV⟩).map e.toRingHom = Ideal.ofList (List.ofFn z) :=
      (Affine.ChartRefinement.ideal U hU φ.toRingHom I).trans hI
    have hb := congrArg (fun J : Ideal S => J.map e.symm.toRingHom) he
    simpa [Ideal.map_map] using hb
  · simpa only [List.length_map, List.length_ofFn] using hlen

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopenLength
