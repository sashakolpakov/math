import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.WeilPointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PulledPolarization

/-! # Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PairingBaseChange.Construction

noncomputable section

section

/-! Base change of the actual Weil value with independent Cartier
representatives. The representatives remain parameters in this comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {S S' : Scheme}
  {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (hD : GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian.scheme)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n) (s : S' ⟶ S)
  [IsFinite ((𝟙 A.scheme) ^ n).left] [Flat ((𝟙 A.scheme) ^ n).left]
  [Surjective ((𝟙 A.scheme) ^ n).left] [LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left]
  [IsFinite ((𝟙 (A.pullback s).scheme) ^ n).left] [Flat ((𝟙 (A.pullback s).scheme) ^ n).left]
  [Surjective ((𝟙 (A.pullback s).scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 (A.pullback s).scheme) ^ n).left]

set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionWeilValue_baseChange
    (C0 : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))
    (C1 : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S' (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 (A.pullback s).scheme) ^ n))))
    (T : Over S') (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    let p0 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction A D pol hD
    let p1 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s) (hD.pullback s)
    letI : IsMonHom (show A.scheme ⟶ p0.dual.abelian from p0.map) := p0.preservesGroup
    letI : IsFinite (show A.scheme ⟶ p0.dual.abelian from p0.map).left := p0.finite
    letI : Flat (show A.scheme ⟶ p0.dual.abelian from p0.map).left := p0.flat
    letI : Surjective (show A.scheme ⟶ p0.dual.abelian from p0.map).left := p0.surjective
    letI : IsMonHom (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map) := p1.preservesGroup
    letI : IsFinite (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map).left := p1.finite
    letI : Flat (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map).left := p1.flat
    letI : Surjective (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map).left := p1.surjective
    let x0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T x
    let y0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y
    FrobeniusKernel.IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue (A.pullback s).scheme p1.representation p1.map n hn C1 T
      (x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso (A.pullback s).scheme n).inv)
      ((y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso (A.pullback s).scheme n).inv) ≫
        CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p1.map n) =
    CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s T
      (FrobeniusKernel.IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.scheme p0.representation p0.map n hn C0 ((Over.map s).obj T)
        (x0 ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.scheme n).inv)
        ((y0 ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.scheme n).inv) ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p0.map n)) := by
  dsimp only
  let D0 := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  let D1 := D0.pullback s
  let ell0 : A.scheme ⟶ D0.withPicardGroup.abelian := pol.isogeny.hom
  let ell1 : (A.pullback s).scheme ⟶ D1.withPicardGroup.abelian := (pol.pullback s).isogeny.hom
  have : IsMonHom ell0 := PolarizationAdapter.Construction.originalPolarization_preserves_canonical_group_of_universal_functions A D pol hD
  have : IsFinite ell0.left := pol.isogeny.finite
  have : Flat ell0.left := pol.isogeny.flat
  have : Surjective ell0.left := pol.isogeny.surjective
  have : IsMonHom ell1 := PulledPolarization.Construction.universalFunction_pulled_polarization_isMonHom D hD pol s
  have : IsFinite ell1.left := (pol.pullback s).isogeny.finite
  have : Flat ell1.left := (pol.pullback s).isogeny.flat
  have : Surjective ell1.left := (pol.pullback s).isogeny.surjective
  have : Smooth ((Over.pullback s).obj A.scheme).hom :=
    inferInstanceAs (Smooth (A.pullback s).scheme.hom)
  have : IsProper ((Over.pullback s).obj A.scheme).hom := (A.pullback s).proper
  have : GeometricallyConnected ((Over.pullback s).obj A.scheme).hom := (A.pullback s).connected
  have : IsFinite ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left :=
    inferInstanceAs (IsFinite ((𝟙 (A.pullback s).scheme) ^ n).left)
  have : Flat ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left :=
    inferInstanceAs (Flat ((𝟙 (A.pullback s).scheme) ^ n).left)
  have : Surjective ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left :=
    inferInstanceAs (Surjective ((𝟙 (A.pullback s).scheme) ^ n).left)
  have : LocallyOfFinitePresentation ((𝟙 ((Over.pullback s).obj A.scheme)) ^ n).left :=
    inferInstanceAs (LocallyOfFinitePresentation ((𝟙 (A.pullback s).scheme) ^ n).left)
  let x0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T x
  let y0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y
  let xp := x ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso (A.pullback s).scheme n).inv
  let yp := (y ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso (A.pullback s).scheme n).inv) ≫
    CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell1 n
  let yq := (y0 ≫ (Torsion.Groups.Construction.torsionEqualizerKernelIso A.scheme n).inv) ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell0 n
  have hy : Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D0.abelian s T (yp ≫ TorsionQuotient.SubgroupFunctor.torsionι D1.withPicardGroup.abelian n) =
      yq ≫ TorsionQuotient.SubgroupFunctor.torsionι D0.withPicardGroup.abelian n := by
    exact WeilPointBaseChange.Construction.universalFunctionWeilImage_baseChange D hD pol n s T y
  have hv := FrobeniusKernel.IntrinsicWeilBaseChange.Construction.nativeWeilPointValue_baseChange s A.scheme D0 ell0 ell1 n hn C0 C1 T xp yp yq hy
  have hx := Intrinsic.TorsionWeilBaseChange.Construction.nativeTorsionOriginalPoint_equalizer s (Grp.mk A.scheme) n T x
  exact hv.trans (congrArg
    (fun a : (Over.map s).obj T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n) =>
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s T
        (FrobeniusKernel.IntrinsicWeilCharacterPoints.Construction.nativeWeilPointValue A.scheme D0 ell0 n hn C0 ((Over.map s).obj T) a yq)) hx)

end

/-! The original canonical polarization pairing commutes with change
on arbitrary bases with universal functions on all scheme-valued torsion points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {S S' : Scheme}
  {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (hD : GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian.scheme)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n) (s : S' ⟶ S)

section Covers
variable
  [IsFinite ((𝟙 A.scheme) ^ n).left]
  [Flat ((𝟙 A.scheme) ^ n).left]
  [Surjective ((𝟙 A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left]
  [IsFinite ((𝟙 (A.pullback s).scheme) ^ n).left]
  [Flat ((𝟙 (A.pullback s).scheme) ^ n).left]
  [Surjective ((𝟙 (A.pullback s).scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 (A.pullback s).scheme) ^ n).left]
  [IsFinite ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left]
  [Flat ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left]
  [Surjective ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left]
  [IsFinite ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left]
  [Flat ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left]
  [Surjective ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left]

set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionNativePolarizationPairing_baseChange_value_of_covers (T : Over S')
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    (PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) (hD.pullback s) n hn).pairValue x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s T
        ((PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A D pol hD n hn).pairValue
          (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T x)
          (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y)) := by
  let p0 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction A D pol hD
  let p1 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s) (hD.pullback s)
  let C0 := FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A) n
  let C1 := FrobeniusKernel.DualityIntrinsicPointValues.Construction.e56NativeKernelCharacterRepresentation (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)) n
  let x0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T x
  let y0 := Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y
  have hv := universalFunctionWeilValue_baseChange D hD pol n hn s C0 C1 T x y
  exact (Relative.IntrinsicWeilValue.Construction.canonicalNativePolarizationPairing_nativePointValue p1 n hn T x y).trans
    (hv.trans (congrArg (CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s T)
      (Relative.IntrinsicWeilValue.Construction.canonicalNativePolarizationPairing_nativePointValue p0 n hn ((Over.map s).obj T) x0 y0).symm))

end Covers

set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionNativePolarizationPairing_baseChange_value (T : Over S')
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    (PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) (hD.pullback s) n hn).pairValue x y =
      CartierDuality.EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange s T
        ((PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A D pol hD n hn).pairValue
          (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T x)
          (Intrinsic.TorsionReferencePoint.Construction.nativeTorsionOriginalPoint s (Grp.mk A.scheme) n T y)) := by
  let p0 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction A D pol hD
  let p1 := PolarizationAdapter.Construction.universalFunctionPolarizationOfHilbertConstruction (A.pullback s) (D.pullback s) (pol.pullback s) (hD.pullback s)
  have : IsMonHom (show A.scheme ⟶ p0.dual.abelian from p0.map) := p0.preservesGroup
  have : IsFinite (show A.scheme ⟶ p0.dual.abelian from p0.map).left := p0.finite
  have : Flat (show A.scheme ⟶ p0.dual.abelian from p0.map).left := p0.flat
  have : Surjective (show A.scheme ⟶ p0.dual.abelian from p0.map).left := p0.surjective
  have : IsMonHom (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map) := p1.preservesGroup
  have : IsFinite (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map).left := p1.finite
  have : Flat (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map).left := p1.flat
  have : Surjective (show (A.pullback s).scheme ⟶ p1.dual.abelian from p1.map).left := p1.surjective
  have h0 := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A.scheme p0.dual p0.map n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := h0.1
  have : Flat ((𝟙 A.scheme) ^ n).left := h0.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := h0.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := h0.2.2.2
  have h1 := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover (A.pullback s).scheme p1.dual p1.map n hn
  have : IsFinite ((𝟙 (A.pullback s).scheme) ^ n).left := h1.1
  have : Flat ((𝟙 (A.pullback s).scheme) ^ n).left := h1.2.1
  have : Surjective ((𝟙 (A.pullback s).scheme) ^ n).left := h1.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 (A.pullback s).scheme) ^ n).left := h1.2.2.2
  have : IsFinite ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left := h0.1
  have : Flat ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left := h0.2.1
  have : Surjective ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left := h0.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction A).toOver) ^ n).left := h0.2.2.2
  have : IsFinite ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left := h1.1
  have : Flat ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left := h1.2.1
  have : Surjective ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left := h1.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 (PolarizationPoincareComparison.Construction.nativeAbelianOfHilbertConstruction (A.pullback s)).toOver) ^ n).left := h1.2.2.2
  exact universalFunctionNativePolarizationPairing_baseChange_value_of_covers D hD pol n hn s T x y

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PairingBaseChange.Construction
