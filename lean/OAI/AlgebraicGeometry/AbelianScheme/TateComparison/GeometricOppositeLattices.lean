import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricWeilBalance
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricWeilPreimages
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SelfDualBlockLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagComposites

/-! # Geometric Opposite Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Each actual composite's opposite lattice is the dual of its
chosen lattice scaled by the inverse cumulative multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {x y : D.GeometricPoint b}
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hf in
theorem Data.SphericalPELAlbaneseData.geometricIsogeny_opposite_lattice {m : ℕ}
    (e : PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ m)) (v : Fin s) :
    Rational.framedTateLattice frame e.isogeny.hom (v, true) =
      ((HeckeKernel.qUnit q) ^ m)⁻¹ •
        (D.framedOppositePairing (D.fiberFamily b x) _ frame
          (D.geometricRationalWeilPairing hg hgeometry b x) v).dualSubmodule
            (Rational.framedTateLattice frame e.isogeny.hom (v, false)) := by
  have hs : (((HeckeKernel.qUnit q) ^ m : ℚ_[q]ˣ) : ℚ_[q]) = (q : ℚ_[q]) ^ m := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  have hL : ((((HeckeKernel.qUnit q) ^ m : ℚ_[q]ˣ) : ℚ_[q]) •
      LinearMap.BilinForm.congr frame (D.geometricRationalWeilPairing hg hgeometry b x)).dualSubmodule
        (Submodule.pi Set.univ (Rational.framedTateLattice frame e.isogeny.hom)) =
      Submodule.pi Set.univ (Rational.framedTateLattice frame e.isogeny.hom) := by
    rw [hs]
    exact D.geometricWeilFramedPreimage_self_dual hg hgeometry e frame hf
  exact SelfDualBlockLattices.oppositeBlockLattice_of_scaled_self_dual
    (LinearMap.BilinForm.congr frame (D.geometricRationalWeilPairing hg hgeometry b x))
    Data.SphericalPELAlbaneseData.oppositeBlock Data.SphericalPELAlbaneseData.oppositeBlock_involutive.injective
    (D.geometricWeilFrame_orthogonal hg hgeometry b x frame hf)
    ((HeckeKernel.qUnit q) ^ m) (Rational.framedTateLattice frame e.isogeny.hom) hL (v, false)

include hf in
theorem Data.SphericalPELAlbaneseData.geometricComposite_opposite_lattice {ts : List (Local.IntegralType s)}
    {F : D.PELFlag b x ts} (p : D.CompositeSystem F) (j : Fin (ts.length + 1)) (v : Fin s) :
    D.compositeLattice frame p j (v, true) =
      (HeckeKernel.qUnit q) ^ (-(Local.cumulativeMultiplier ts j)) •
        (D.framedOppositePairing (D.fiberFamily b x) _ frame
          (D.geometricRationalWeilPairing hg hgeometry b x) v).dualSubmodule
            (D.compositeLattice frame p j (v, false)) := by
  have hm : ((HeckeKernel.qUnit q) ^ Data.SphericalPELAlbaneseData.flagMultiplier ts j)⁻¹ = (HeckeKernel.qUnit q) ^ (-(Local.cumulativeMultiplier ts j)) := by
    rw [zpow_neg, ← zpow_natCast, Int.toNat_of_nonneg (FlagComposites.cumulativeMultiplier_nonneg ts j)]
  exact (D.geometricIsogeny_opposite_lattice hg hgeometry frame hf (p j) v).trans
    (congrArg (fun z => z •
      (D.framedOppositePairing (D.fiberFamily b x) _ frame
        (D.geometricRationalWeilPairing hg hgeometry b x) v).dualSubmodule
          (D.compositeLattice frame p j (v, false))) hm)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
