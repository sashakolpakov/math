import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace

/-! # Top Form Trace Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTraceData

noncomputable section

/-! The normalized top-form trace and its proved bijectivity are
packaged together before specializing to a chosen projective model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R]
  (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  {n : ℕ} (f : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion f.left]
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)

def data : {τ : TopFormTrace.cohomology X f g →+
    Projective.TopTracePairing.coefficientRing R // Function.Bijective τ} :=
  ⟨TopFormTrace.trace X f B hB g,
    TopFormTrace.trace_bijective X f B hB g s hs⟩

theorem map_eq : (data X f B hB g s hs).val = TopFormTrace.trace X f B hB g := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTraceData
