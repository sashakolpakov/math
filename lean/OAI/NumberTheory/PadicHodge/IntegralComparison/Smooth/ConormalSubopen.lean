import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSubopenLength
import OAI.NumberTheory.PadicHodge.IntegralComparison.RingTransportedConormalBasis

/-! # Conormal Subopen -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalSubopen

noncomputable section

/-! A smooth closed center admits actual affine subopens with regular
equations and the matching conormal basis. The basis is transported
from the genuine pointed smooth frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens) (hU : IsAffineOpen U)
  {k : Type u} [CommRing k] [Algebra k Γ(X, U)] [IsNoetherianRing Γ(X, U)]
  [Algebra.Smooth k Γ(X, U)] [Algebra.Smooth k (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩)]

theorem exists_subopen (p : PrimeSpectrum (Γ(X, U) ⧸ I.ideal ⟨U, hU⟩)) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V), V ≤ U ∧
      hU.fromSpec (p.comap (Ideal.Quotient.mk (I.ideal ⟨U, hU⟩))) ∈ V ∧
      ∃ (c : ℕ) (s : Fin c → Γ(X, V))
        (hs : Koszul.OrientedTopCohomology.ideal Γ(X, V) s = I.ideal ⟨V, hV⟩),
        RingTheory.Sequence.IsRegular Γ(X, V) (List.ofFn s) ∧
        ∃ b : Module.Basis (Fin c) (Γ(X, V) ⧸ I.ideal ⟨V, hV⟩) (I.ideal ⟨V, hV⟩).Cotangent,
          (∀ j, b j = (I.ideal ⟨V, hV⟩).toCotangent
            (ConormalKoszulPurity.conormalVectors Γ(X, V) (I.ideal ⟨V, hV⟩) s hs j)) ∧
          c = Module.rankAtStalk Ω[Γ(X, U)⁄k]
              (p.comap (Ideal.Quotient.mk (I.ideal ⟨U, hU⟩))) -
            Module.rankAtStalk Ω[Γ(X, U) ⧸ I.ideal ⟨U, hU⟩⁄k] p := by
  obtain ⟨S, hSk, hSs, φ, hφ, q, hq, c, z, D, hD, hI, hreg, hlen⟩ :=
    RegularSequenceLength.exists_pointed_open_regular_sequence
      (k := k) (I.ideal ⟨U, hU⟩) p
  let := hSk
  let := hSs
  let := hφ
  let V := Affine.ChartRefinement.openSet U hU φ.toRingHom
  let hV : IsAffineOpen V := Affine.ChartRefinement.affine U hU φ.toRingHom
  let e : Γ(X, V) ≃+* S :=
    (Affine.ChartRefinement.sectionsIso U hU φ.toRingHom).commRingCatIsoToRingEquiv
  have hIe : (I.ideal ⟨V, hV⟩).map e.toRingHom = Ideal.span (Set.range z) := by
    change (I.ideal ⟨V, hV⟩).map
      (Affine.ChartRefinement.sectionsIso U hU φ.toRingHom).hom.hom = _
    simpa only [RegularSequence.CoordinateRegularity.ofList_ofFn] using
      (Affine.ChartRefinement.ideal U hU φ.toRingHom I).trans hI
  let s : Fin c → Γ(X, V) := fun j => e.symm (z j)
  have hs : Koszul.OrientedTopCohomology.ideal Γ(X, V) s = I.ideal ⟨V, hV⟩ :=
    RingTransportedConormalBasis.generates e (I.ideal ⟨V, hV⟩) z hIe
  refine ⟨V, hV, Affine.ChartRefinement.le U hU φ.toRingHom, ?_, c, s, hs, ?_,
    RingTransportedConormalBasis.basis e (I.ideal ⟨V, hV⟩) z D hD hIe, ?_, hlen⟩
  · refine ⟨q, trivial, ?_⟩
    change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ.toRingHom)) q) = _
    exact congrArg hU.fromSpec hq
  · simpa only [s, List.map_ofFn, Function.comp_def] using
      RegularSubopen.regular_map e.symm (List.ofFn z) hreg
  · intro j
    rw [RingTransportedConormalBasis.basis_apply]
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ConormalSubopen
