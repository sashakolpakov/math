import OAI.RepresentationTheory.Theta.Geometric.Cleared.ComplementType
import OAI.RepresentationTheory.Theta.Geometric.UnshiftPELTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricSplitFrame

/-! # Reverse Cleared Branch -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReverseClearedBranch

noncomputable section

/-! Every actual cleared active branch reverses to an actual branch of
the reversed weight, with the literal original source as corrected endpoint. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
variable {E K k : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [Field k] [CharZero k] [IsAlgClosed k]
    {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (A : TateComparison.Action D) (hA : A.IsRealization D hg hgood hIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    {b : Spec (.of k) ⟶ Spec (.of K)}

attribute [local irreducible] AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberFamily
  AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.geometricSplitFrame AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.transportFrame UnshiftPELTransport.unshiftTransport

include hA hdegree hs in
theorem reverse_cleared_branch (a : Intrinsic.Hecke.ActiveWeight) (x y : D.GeometricPoint b)
    (c : (D.correspondence (Intrinsic.Hecke.clearedActiveType D.reference.distinguished a)).Fiber x)
    (hc : c.val ≫ (D.correspondence (Intrinsic.Hecke.clearedActiveType D.reference.distinguished a)).target =
      (fun z : D.GeometricPoint b => z ≫ A.shift.hom)^[Intrinsic.Hecke.clearingExponent D.reference.distinguished a] y) :
    ∃ d : (D.correspondence (Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a))).Fiber y,
      d.val ≫ (D.correspondence (Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a))).target =
        (fun z : D.GeometricPoint b => z ≫ A.shift.hom)^[
          Intrinsic.Hecke.clearingExponent D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a)] x := by
  let n := Intrinsic.Hecke.clearingExponent D.reference.distinguished a
  let z := (fun w : D.GeometricPoint b => w ≫ A.shift.hom)^[n] y
  let z' := (fun w : D.GeometricPoint b => w ≫ A.shift.hom)^[n] x
  let frame := D.geometricSplitFrame hgood hdegree hs hg b z
  have hf := D.geometricSplitFrame_equivariant hgood hdegree hs hg b z
  let u := (ZMod.unitOfCoprime q hgood.2.2.1) ^ n
  obtain ⟨j⟩ := ConcreteShiftFiber.actual_shift_iterate_fiber D hg hgood hIsogenyQuotient A hA y n
  obtain ⟨kIso⟩ := ConcreteShiftFiber.actual_shift_iterate_fiber D hg hgood hIsogenyQuotient A hA x n
  have hu : ZMod.unitOfCoprime (q ^ (2 * n)) (hgood.2.2.1.pow_left (2 * n)) = u * u := by
    rw [Cleared.FiberMarking.unitOfCoprime_pow, show 2 * n = n + n by omega, pow_add]
  have H := Cleared.ComplementType.cleared_complement_type D hg hgood hIsogenyQuotient a x z c.val c.property hc frame hf
  change ∃ f : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b z)
      ((D.fiberFamily b x).shiftMarking (ZMod.unitOfCoprime (q ^ (2 * n)) (hgood.2.2.1.pow_left (2 * n))))
      (q ^ (2 * n)), _ at H
  rw [hu] at H
  obtain ⟨f, hpos⟩ := H
  let frame' : D.FiberFrame b y := j.transportFrame (Over.mk (𝟙 (Spec (.of k)))) frame
  have hf' := UnshiftPELTransport.unshiftFrame_equivariant (s := s) (q := q)
    (Q := D.fiberFamily b y) (Y := D.fiberFamily b z)
    (Over.mk (𝟙 (Spec (.of k)))) u j D.localCharacter frame hf
  have hl (v : Fin s) : D.framedFiberSourceLattice b y frame' (v, false) =
      D.framedFiberSourceLattice b z frame (v, false) := by
    apply Subtype.ext
    have h := UnshiftPELTransport.pelFrameTransport_sourceIntegral (s := s) (q := q)
      (P := (D.fiberFamily b y).shiftMarking u) (Q := D.fiberFamily b z)
      (Over.mk (𝟙 (Spec (.of k)))) j frame (v, false)
    simpa only [AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.framedFiberSourceLattice,
      AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.framedSourceLattice, PowerTatePreimages.framedSourceIntegral,
      AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData.shiftMarking] using h
  have Hf : ∃ e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b y) (D.fiberFamily b z')
      (q ^ (Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a)).multiplierNat),
      ∀ v, ∃ L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q],
        AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame' e.isogeny.hom (v, false) = L.val ∧
        AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q])
          ((Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a)).val.exponent v)
          (D.framedFiberSourceLattice b y frame' (v, false)) L := by
    rw [Active.CosetFiberBranch.clearedActiveType_multiplierNat, ReverseActiveWeight.reverse_clearingExponent]
    refine ⟨UnshiftPELTransport.unshiftTransport u f j kIso, fun v => ?_⟩
    obtain ⟨L, hL, hp⟩ := hpos v
    refine ⟨L, (UnshiftPELTransport.unshiftTransport_framedLattice _ u f j kIso frame (v, false)).trans hL, ?_⟩
    rwa [hl]
  obtain ⟨e, he⟩ := Hf
  obtain ⟨d, hd⟩ := TypedIsogenyBranch.exists_original_branch_of_typed_isogeny D hg hgood hIsogenyQuotient hdegree hs
    (Intrinsic.BranchLattices.padicTateComparisonLatticeInput q) y z' frame' hf'
    (Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a)) e he
  refine ⟨d, ?_⟩
  simpa only [ReverseActiveWeight.reverse_clearingExponent] using hd

end

end OAI.RepresentationTheory.Theta.Geometric.ReverseClearedBranch
