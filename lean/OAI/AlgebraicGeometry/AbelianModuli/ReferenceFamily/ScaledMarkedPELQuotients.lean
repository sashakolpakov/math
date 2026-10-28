import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedIsogenies
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodSimilitude
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.LatticeMapLevelComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients

/-! # Scaled Marked PEL Quotients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedPELQuotients

noncomputable section

/-! Cleared marked Hodge isometries produce actual paired PEL
quotients on the original complex schemes. The polarization multiplier,
integral action, and full ordered level are derived from the exact
period and lattice maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [CharZero K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (t : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of K)) (A B : PEL.Objects.PELObject P iota N (Over.mk t))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (ξ : E) (hξ : ξ ≠ 0) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

include hξ in
omit [CharZero K] [NeZero N] in
private theorem scaledMarkedQuotient_polarization
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B.polarized B.action s hs rfl hdegree B.rosati ξ) (u x) (u y) =
        Datum.RankThreePELDatum.matrixHermitian
          (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati ξ) x y)
    (D : ℕ)
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian)
    (hf : Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A.polarized.abelian B.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) f.hom =
      D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.polarized.abelian B.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        A.action B.action s hs rfl hdegree u).toLinearMap) :
    AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f.hom
      A.polarized.dual B.polarized.dual B.polarized.polarization =
        A.polarized.polarization.isogeny.hom ^ (D ^ 2) := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized
  apply Polarization.PeriodSimilitude.polarization_pullback_of_period_similitude A.polarized B.polarized f.hom (D ^ 2)
  intro x y
  change Intrinsic.ChernPairing.nativePolarizationForm B.polarized
      (Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A.polarized.abelian B.polarized.abelian PA PB f.hom x)
      (Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A.polarized.abelian B.polarized.abelian PA PB f.hom y) =
    D ^ 2 • Intrinsic.ChernPairing.nativePolarizationForm A.polarized x y
  rw [hf]
  exact ScaledMarkedPeriodTransport.NativeHermitianMarking.scaledMarkedPeriodTransport_polarization A.polarized B.polarized A.action B.action
    s hs rfl hdegree A.rosati B.rosati ξ hξ u hu D x y

omit [CharZero K] [NeZero N] in
private theorem scaledMarkedQuotient_rationalLift (D : ℕ) (hD : 0 < D)
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian)
    (hf : Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A.polarized.abelian B.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) f.hom =
      D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.polarized.abelian B.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        A.action B.action s hs rfl hdegree u).toLinearMap) :
    Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)).hom ≫ f.hom ≫
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)).inv) =
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.polarized.abelian B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        A.action B.action s hs rfl hdegree (ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedCoordinateIso u D hD)).toLinearMap := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized
  have := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.polarized.abelian B.polarized.abelian PA PB f.hom
  exact (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ (Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeComparisonMap_eq A.polarized.abelian B.polarized.abelian PA PB f.hom)).trans (hf.trans (ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedCoordinateIso_periods A.polarized.abelian B.polarized.abelian PA PB
    A.action B.action s hs rfl hdegree u D hD).symm)

include hξ in
private theorem pairedQuotient_of_scaled_isogenies
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B.polarized B.action s hs rfl hdegree B.rosati ξ) (u x) (u y) =
        Datum.RankThreePELDatum.matrixHermitian
          (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati ξ) x y)
    (D : ℕ) (hD : 0 < D) (hmod : Nat.ModEq N (D ^ 2) 1)
    (m : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
        A.action s hs rfl hdegree →ₗ[ℤ]
      Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        B.action s hs rfl hdegree)
    (hm : ∀ x, (m x).val = D • u x.val)
    (hlevel : ∀ c, LatticeDivision.TorusTorsion.modNMap N m.toAddMonoidHom
      (Intrinsic.OrderedLatticeLevel.markedOrderedLatticeLevel A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
        A.action s hs rfl hdegree A.polarized.level c) =
      Intrinsic.OrderedLatticeLevel.markedOrderedLatticeLevel B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        B.action s hs rfl hdegree B.polarized.level c)
    (f : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian)
    (v : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B.polarized.abelian A.polarized.abelian)
    (hfe : Etale f.hom.left)
    (hfv : f.hom ≫ v.hom = (𝟙 A.polarized.abelian.scheme) ^ (D ^ 2))
    (hvf : v.hom ≫ f.hom = (𝟙 B.polarized.abelian.scheme) ^ (D ^ 2))
    (hf : Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A.polarized.abelian B.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) f.hom =
      D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.polarized.abelian B.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        A.action B.action s hs rfl hdegree u).toLinearMap)
    (hv : Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap B.polarized.abelian A.polarized.abelian
      (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) v.hom =
      D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B.polarized.abelian A.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
        B.action A.action s hs rfl hdegree u.symm).toLinearMap)
    (hfact : ∀ a, A.action.map a ≫ f.hom = f.hom ≫ B.action.map a) :
    ∃ q : Paired.PELQuotients.PairedPELQuotient A B (D ^ 2),
      CrossPoincarePeriodMaps.polarizedAbelianPeriodMap A.polarized B.polarized q.forward.isogeny.hom =
        D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.polarized.abelian B.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
          A.action B.action s hs rfl hdegree u).toLinearMap ∧
      CrossPoincarePeriodMaps.polarizedAbelianPeriodMap B.polarized A.polarized q.reverse.isogeny.hom =
        D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B.polarized.abelian A.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
          B.action A.action s hs rfl hdegree u.symm).toLinearMap := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized
  have hpol := scaledMarkedQuotient_polarization (t := t) (A := A) (B := B)
    (hs := hs) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (u := u) hu D f hf
  have hfn := scaledMarkedQuotient_rationalLift (t := t) (A := A) (B := B)
    (hs := hs) (hdegree := hdegree) (u := u) D hD f hf
  let q : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient A B (D ^ 2) := {
    isogeny := f
    etale := hfe
    polarization := hpol
    action := fun a => (hfact a).symm
    marking := Marked.LatticeMapLevelComparison.level_comparison_of_marked_lattice_map A.polarized.abelian B.polarized.abelian
      PA PB A.action B.action s hs rfl hdegree A.polarized.level B.polarized.level f.hom
      (ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedCoordinateIso u D hD) m
      (fun x => (hm x).trans (ScaledMarkedPeriodTransport.NativePELMarking.scaledMarkedCoordinateIso_apply u D hD x.val).symm) hfn hlevel }
  have : IsLocallyNoetherian (Over.mk t).left := inferInstanceAs (IsLocallyNoetherian Foundations.Scheme.ProjectiveSpace.complexBase)
  let r := Paired.PELQuotients.scalarComplementPELQuotient q v (pow_pos hD 2) hmod hfv hvf
  exact ⟨{
    forward := q
    reverse := r
    forward_reverse := hfv
    reverse_forward := hvf }, hf, hv⟩

include hξ in
theorem exists_paired_quotient_of_scaled_marked_hodge_isometry
    (huH : ComplexMultiplication.WeightOne.CM.IsHodgeMap
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)))
      (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.polarized.abelian B.polarized.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        A.action B.action s hs rfl hdegree u).toLinearMap)
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B.polarized B.action s hs rfl hdegree B.rosati ξ) (u x) (u y) =
        Datum.RankThreePELDatum.matrixHermitian
          (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree A.rosati ξ) x y)
    (D : ℕ) (hD : 0 < D) (hmod : Nat.ModEq N (D ^ 2) 1)
    (m : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
        A.action s hs rfl hdegree →ₗ[ℤ]
      Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        B.action s hs rfl hdegree)
    (m' : Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        B.action s hs rfl hdegree →ₗ[ℤ]
      Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
        A.action s hs rfl hdegree)
    (hm : ∀ x, (m x).val = D • u x.val)
    (hm' : ∀ x, (m' x).val = D • u.symm x.val)
    (hlevel : ∀ c, LatticeDivision.TorusTorsion.modNMap N m.toAddMonoidHom
      (Intrinsic.OrderedLatticeLevel.markedOrderedLatticeLevel A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
        A.action s hs rfl hdegree A.polarized.level c) =
      Intrinsic.OrderedLatticeLevel.markedOrderedLatticeLevel B.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
        B.action s hs rfl hdegree B.polarized.level c) :
    ∃ q : Paired.PELQuotients.PairedPELQuotient A B (D ^ 2),
      CrossPoincarePeriodMaps.polarizedAbelianPeriodMap A.polarized B.polarized q.forward.isogeny.hom =
        D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.polarized.abelian B.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized)
          A.action B.action s hs rfl hdegree u).toLinearMap ∧
      CrossPoincarePeriodMaps.polarizedAbelianPeriodMap B.polarized A.polarized q.reverse.isogeny.hom =
        D • (Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport B.polarized.abelian A.polarized.abelian
          (Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized) (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
          B.action A.action s hs rfl hdegree u.symm).toLinearMap := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B.polarized
  obtain ⟨f, v, hfe, _, hfv, hvf, hf, hv, hfact, _⟩ :=
    ScaledMarkedIsogenies.exists_exact_scaled_marked_isogenies A.polarized.abelian B.polarized.abelian PA PB
      A.action B.action s hs rfl hdegree u huH D hD m m' hm hm'
  exact pairedQuotient_of_scaled_isogenies (t := t) (A := A) (B := B)
    (hs := hs) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (u := u)
    hu D hD hmod m hm hlevel f v hfe hfv hvf hf hv hfact

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ScaledMarkedPELQuotients
