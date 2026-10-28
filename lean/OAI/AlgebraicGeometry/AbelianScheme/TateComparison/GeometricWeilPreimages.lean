import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilNaturality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELWeilSelfDuality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearDualTransport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedPreimageDecomposition

/-! # Geometric Weil Preimages -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual lattice preimage of every geometric PEL isogeny is
self-dual for the source Weil pairing scaled by its multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  {b : Spec (.of k) ⟶ Spec (.of K)} {x y : D.GeometricPoint b} {m : ℕ}
  (e : PELIsogenies.PELIsogeny (D.fiberFamily b x) (D.fiberFamily b y) (q ^ m))

theorem Data.SphericalPELAlbaneseData.geometricWeilPreimage_self_dual :
    ((q : ℚ_[q]) ^ m • D.geometricRationalWeilPairing hg hgeometry b x).dualSubmodule
        (Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom) =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom := by
  apply SimilitudeDualLattice.dualSubmodule_comap_of_self_dual _ (D.geometricRationalWeilPairing hg hgeometry b y)
    (GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny)
  · intro v w
    have he := e.rationalWeil_similitude D.reference.polarizationType
      (D.fiberPolarizationType hgeometry b x) q hg.2.2.2.2
      (D.fiberFamily b y) D.reference.polarizationType
      (D.fiberPolarizationType hgeometry b y) hg.2.2.2.2 v w
    change D.geometricRationalWeilPairing hg hgeometry b y
      ((GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny).toLinearMap v)
      ((GeometricIsogeny.geometricTateIsogenyEquiv (𝟙 (Spec (.of k))) q e.isogeny).toLinearMap w) = _
    rw [GeometricIsogeny.geometricTateIsogenyEquiv_toLinearMap]
    simpa only [Data.SphericalPELAlbaneseData.geometricRationalWeilPairing, Data.SphericalPELAlbaneseData.geometricTateWeilPairing, nsmul_eq_mul, Nat.cast_pow] using he
  · exact D.geometricRationalWeilPairing_self_dual hg hgeometry b y

variable (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)

include hf in
theorem Data.SphericalPELAlbaneseData.geometricWeilFramedPreimage_self_dual :
    ((q : ℚ_[q]) ^ m • LinearMap.BilinForm.congr frame
        (D.geometricRationalWeilPairing hg hgeometry b x)).dualSubmodule
          (Submodule.pi Set.univ (Rational.framedTateLattice frame e.isogeny.hom)) =
      Submodule.pi Set.univ (Rational.framedTateLattice frame e.isogeny.hom) := by
  have hc : LinearMap.BilinForm.congr frame
      ((q : ℚ_[q]) ^ m • D.geometricRationalWeilPairing hg hgeometry b x) =
        (q : ℚ_[q]) ^ m • LinearMap.BilinForm.congr frame
          (D.geometricRationalWeilPairing hg hgeometry b x) := by
    ext v w
    rfl
  have h := BilinearDualTransport.bilinearSelfDual_congr
    ((q : ℚ_[q]) ^ m • D.geometricRationalWeilPairing hg hgeometry b x) frame _
    (D.geometricWeilPreimage_self_dual hg hgeometry e)
  rw [hc, D.framedTatePreimage_eq_pi hg e frame hf D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
