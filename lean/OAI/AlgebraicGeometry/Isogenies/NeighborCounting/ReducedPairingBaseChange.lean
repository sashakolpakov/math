import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingIntrinsicValues
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.PolarizationPointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeFlip

/-! # Reduced Pairing Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPairingBaseChange

noncomputable section

/-! The original canonical polarization pairing commutes with arbitrary
base change between reduced locally Noetherian schemes. All multiplication
covers and all dual-point comparisons are constructed from the source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingIntrinsicValues.Intrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.TorsionPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.PolarizationPointBaseChange
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative
  AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange.Construction.nativeTorsionPullback_commutative Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom
attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative
  AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56PointPolarization_preserves

variable {S T : Scheme} [IsReduced S] [IsLocallyNoetherian S]
  [IsReduced T] [IsLocallyNoetherian T] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ}
  (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (s : T ⟶ S) (n : ℕ) (hn : 0 < n)

theorem reducedCanonicalPairing_value_baseChange (Q : Over T)
    (x y : Q ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).pairValue x y =
      AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
        ((AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A D pol n hn).pairValue
          (Intrinsic.TorsionPointBaseChange.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n Q x)
          (Intrinsic.TorsionPointBaseChange.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n Q y)) := by
  let A₀ : CartierDuality.PolarizedTorsion.AbelianScheme S := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A
  let p₀ : CartierDuality.PolarizedTorsion.Polarization A₀ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction A D pol
  let A₁ : CartierDuality.PolarizedTorsion.AbelianScheme T := AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)
  let p₁ : CartierDuality.PolarizedTorsion.Polarization A₁ :=
    AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBasePolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s)
  let D₀ := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  let D₁ := D₀.pullback s
  let ell₀ : A.scheme ⟶ D₀.withPicardGroup.abelian := pol.isogeny.hom
  let ell₁ : (Over.pullback s).obj A.scheme ⟶ D₁.withPicardGroup.abelian :=
    (pol.pullback s).isogeny.hom
  have : IsMonHom ell₀ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.originalPolarization_preserves_canonical_group_over_reduced_base A D pol
  have : IsFinite ell₀.left := pol.isogeny.finite
  have : Flat ell₀.left := pol.isogeny.flat
  have : Surjective ell₀.left := pol.isogeny.surjective
  have : IsMonHom ell₁ := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.originalPolarization_preserves_canonical_group_over_reduced_base
    (A.pullback s) (D.pullback s) (pol.pullback s)
  have : IsFinite ell₁.left := (pol.pullback s).isogeny.finite
  have : Flat ell₁.left := (pol.pullback s).isogeny.flat
  have : Surjective ell₁.left := (pol.pullback s).isogeny.surjective
  have : Smooth ((Over.pullback s).obj A.scheme).hom :=
    inferInstanceAs (Smooth (A.pullback s).scheme.hom)
  have : IsProper ((Over.pullback s).obj A.scheme).hom :=
    inferInstanceAs (IsProper (A.pullback s).scheme.hom)
  have : GeometricallyConnected ((Over.pullback s).obj A.scheme).hom :=
    inferInstanceAs (GeometricallyConnected (A.pullback s).scheme.hom)
  have h₀ := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.scheme D₀.withPicardGroup ell₀ n hn
  have h₁ := AbelianScheme.CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover
    ((Over.pullback s).obj A.scheme) D₁.withPicardGroup ell₁ n hn
  have : IsFinite ((𝟙 A₀.toOver) ^ n).left := h₀.1
  have : Flat ((𝟙 A₀.toOver) ^ n).left := h₀.2.1
  have : Surjective ((𝟙 A₀.toOver) ^ n).left := h₀.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A₀.toOver) ^ n).left := h₀.2.2.2
  have : IsFinite ((𝟙 A₁.toOver) ^ n).left := h₁.1
  have : Flat ((𝟙 A₁.toOver) ^ n).left := h₁.2.1
  have : Surjective ((𝟙 A₁.toOver) ^ n).left := h₁.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A₁.toOver) ^ n).left := h₁.2.2.2
  have : IsFinite ((𝟙 A.scheme) ^ n).left := h₀.1
  have : Flat ((𝟙 A.scheme) ^ n).left := h₀.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := h₀.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := h₀.2.2.2
  have : IsFinite ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left := h₁.1
  have : Flat ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left := h₁.2.1
  have : Surjective ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left := h₁.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left := h₁.2.2.2
  let C₀ := AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation A₀ n
  let C₁ := AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation A₁ n
  let x₀ := Intrinsic.TorsionPointBaseChange.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n Q x
  let y₀ := Intrinsic.TorsionPointBaseChange.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n Q y
  let xp := x ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A₁.toOver) n).inv.hom.hom
  let yp := y ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A₁.toOver) n).inv.hom.hom
  let yd := (y₀ ≫ (AbelianScheme.IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A₀.toOver) n).inv.hom.hom) ≫
    AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell₀ n
  have hb := AbelianScheme.FrobeniusKernel.IntrinsicWeilBaseChange.Construction.nativeWeilPointValue_baseChange s A.scheme D₀ ell₀ ell₁ n hn
    C₀ C₁ Q xp (yp ≫ AbelianScheme.CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell₁ n) yd
    (Intrinsic.PolarizationPointBaseChange.reducedPolarizationPoint_baseChange A D pol s n Q y)
  have hx := Intrinsic.TorsionPointBaseChange.nativeMultiplicationPoint_baseChange s (Grp.mk A.scheme) n Q x
  have hv₀ := Canonical.PairingIntrinsicValues.Intrinsic.canonicalPolarizationPairing_nativePointValue A₀ p₀ n hn ((Over.map s).obj Q) x₀ y₀
  have hv₁ := Canonical.PairingIntrinsicValues.Intrinsic.canonicalPolarizationPairing_nativePointValue A₁ p₁ n hn Q x y
  have hc := congrArg (fun z => AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q
    (AbelianScheme.FrobeniusKernel.IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.scheme D₀ ell₀ n hn C₀
      ((Over.map s).obj Q) z yd)) hx
  exact hv₁.trans (hb.trans (hc.trans
    (congrArg (AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s Q) hv₀.symm)))

theorem reducedCanonicalPairing_baseChange :
    AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn =
      AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback s (Grp.mk A.scheme) (Grp.mk A.scheme) n
        (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A D pol n hn) := by
  apply AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro Q x y
  exact (reducedCanonicalPairing_value_baseChange A D pol s n hn Q x y).trans
    (AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback_value s (Grp.mk A.scheme) (Grp.mk A.scheme) n
      (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A D pol n hn) Q x y).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPairingBaseChange
