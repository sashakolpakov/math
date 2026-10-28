import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveFormTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Pushforward

/-! # Top Form Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace

noncomputable section

/-! The normalized Serre trace, on the literal native Čech cohomology
of top differential forms on the projective coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1))

def cover (i : ULift.{u} (Fin (n + 2))) : X.left.Opens :=
  f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover i

theorem cover_affine [IsClosedImmersion f.left] (i : ULift.{u} (Fin (n + 2))) :
    IsAffineOpen (cover X f i) :=
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen i).preimage f.left

theorem cover_top : ⨆ i, cover X f i = ⊤ := by
  apply top_unique
  intro x _
  have hx : f.left x ∈ ⨆ i : ULift.{u} (Fin (n + 2)), AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) i := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

abbrev cohomology (g : ℕ) : ModuleCat.{u} R :=
  (ModuleCech.DimensionBound.complex R X (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
    (cover X f)).homology g

variable [IsNoetherianRing R] [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R]
  [Nonempty X.left] [IsClosedImmersion f.left]
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]

def serreIso : AddCommGrpCat.of (cohomology X f g) ≅ Smooth.ProjectiveFormTrace.cohomology X f g :=
  ModuleCech.Pushforward.Comparison.cohomologyIso R X (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) f
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R)) g

def trace : cohomology X f g →+ Projective.TopTracePairing.coefficientRing R :=
  ((serreIso X f g).hom ≫ Smooth.ProjectiveFormTrace.trace X f B hB g).hom

variable (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)

def traceIso : cohomology X f g ≃+ Projective.TopTracePairing.coefficientRing R :=
  ((serreIso X f g) ≪≫ Smooth.ProjectiveFormTrace.traceIso X f B hB g s hs).addCommGroupIsoToAddEquiv

theorem traceIso_apply (x : cohomology X f g) :
    traceIso X f B hB g s hs x = trace X f B hB g x := by
  change ((serreIso X f g).hom ≫ (Smooth.ProjectiveFormTrace.traceIso X f B hB g s hs).hom) x = _
  rw [Smooth.ProjectiveFormTrace.traceIso_hom]
  rfl

include s hs in
theorem trace_bijective : Function.Bijective (trace X f B hB g) := by
  have h : (traceIso X f B hB g s hs : cohomology X f g → Projective.TopTracePairing.coefficientRing R) = trace X f B hB g :=
    funext (traceIso_apply X f B hB g s hs)
  rw [← h]
  exact (traceIso X f B hB g s hs).bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace
