import OAI.RepresentationTheory.Theta.Geometric.IsogenyQuotientRelativePosition
import OAI.RepresentationTheory.Theta.Geometric.ReverseActiveWeight
import OAI.RepresentationTheory.Theta.Geometric.Active.CosetFiberBranch

/-! # Complement Type -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cleared.ComplementType

noncomputable section

/-! The full marked complement of an original cleared active branch has
exactly the original cleared type of the reversed active weight. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
variable {E K k : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [Field k] [CharZero k] [IsAlgClosed k]
    {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hgood : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    {b : Spec (.of k) ⟶ Spec (.of K)} (a : Intrinsic.Hecke.ActiveWeight)
    (x y : D.GeometricPoint b)
    (c : Over.mk b ⟶ (D.correspondence (Intrinsic.Hecke.clearedActiveType D.reference.distinguished a)).cover)
    (hsource : c ≫ (D.correspondence (Intrinsic.Hecke.clearedActiveType D.reference.distinguished a)).source = x)
    (htarget : c ≫ (D.correspondence (Intrinsic.Hecke.clearedActiveType D.reference.distinguished a)).target = y)
    (frame : D.FiberFrame b y)
    (hf : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame (D.fiberFamily b y) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hg hIsogenyQuotient hsource htarget hf in
theorem cleared_complement_type :
    let n := Intrinsic.Hecke.clearingExponent D.reference.distinguished a
    ∃ f : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b y)
      ((D.fiberFamily b x).shiftMarking (ZMod.unitOfCoprime (q ^ (2 * n)) (hgood.2.2.1.pow_left (2 * n))))
      (q ^ (2 * n)),
      ∀ v, ∃ L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q],
        AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame f.isogeny.hom (v, false) = L.val ∧
        AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q])
          ((Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a)).val.exponent v)
          (D.framedFiberSourceLattice b y frame (v, false)) L := by
  let t := Intrinsic.Hecke.clearedActiveType D.reference.distinguished a
  let e := D.c46FiberIsogeny hIsogenyQuotient t x y c hsource htarget
  let f := MarkedPELComplement.markedPELComplement e D.reference.polarizationType
    (D.fiberPolarizationType hg b x) (D.fiberPolarizationType hg b y)
    hgood.2.2.2.2 hgood.2.2.1
  have H : ∃ f' : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (D.fiberFamily b y)
      ((D.fiberFamily b x).shiftMarking (ZMod.unitOfCoprime (q ^ t.multiplierNat)
        (hgood.2.2.1.pow_left t.multiplierNat))) (q ^ t.multiplierNat),
      ∀ v, ∃ L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q],
        AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame f'.isogeny.hom (v, false) = L.val ∧
        AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q])
          ((Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a)).val.exponent v)
          (D.framedFiberSourceLattice b y frame (v, false)) L := by
    refine ⟨f, fun v => ?_⟩
    obtain ⟨L, hL, hp⟩ := IsogenyQuotientRelativePosition.c46_complement_relativePosition D hg hgood hIsogenyQuotient t x y c hsource htarget frame hf v
    refine ⟨L, hL, ?_⟩
    have he : (fun i => (t.multiplierNat : ℤ) - t.val.exponent v (Fin.rev i)) =
        (Intrinsic.Hecke.clearedActiveType D.reference.distinguished (ReverseActiveWeight.reverseActiveWeight a)).val.exponent v := by
      funext i
      rw [ReverseActiveWeight.reverse_cleared_exponent, Active.CosetFiberBranch.clearedActiveType_multiplierNat]
      norm_cast
    rwa [he] at hp
  have ht : t.multiplierNat = 2 * Intrinsic.Hecke.clearingExponent D.reference.distinguished a :=
    Active.CosetFiberBranch.clearedActiveType_multiplierNat _ a
  rw [ht] at H
  exact H

end

end OAI.RepresentationTheory.Theta.Geometric.Cleared.ComplementType
