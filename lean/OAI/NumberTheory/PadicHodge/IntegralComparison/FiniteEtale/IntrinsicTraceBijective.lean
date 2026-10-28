import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FiniteEtaleProperTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTraceBijective
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveNaturality

/-! # Intrinsic Trace Bijective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.IntrinsicTraceBijective.Intrinsic

noncomputable section

/-! Finite étale transfer is an isomorphism on native top-form
cohomology on any affine cover, using a projective embedding only
for the target. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem bijective_of_traces {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A → B) (a : B ≃+ C) (b : A ≃+ C)
    (h : ∀ x, a (f x) = b x) : Function.Bijective f := by
  constructor
  · intro x y hxy
    exact b.injective ((h x).symm.trans ((congrArg a hxy).trans (h y)))
  · intro y
    exact ⟨b.symm (a y), a.injective ((h _).trans (b.apply_symm_apply _))⟩

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion i.left]
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g X.hom] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [SmoothOfRelativeDimension g Y.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)
local notation "U₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TopFormTrace.cover X i

include hs in
omit [IsNoetherianRing R] [IsArtinianRing R] [IsLocalRing R] [Module.Injective R R]
  [Nonempty X.left] [IsFinite f.left] [Etale f.left] [Smooth X.hom] [IsProper X.hom]
  [GeometricallyConnected X.hom] [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom] in
theorem section_over : (s ≫ f.left) ≫ X.hom = 𝟙 _ := by
  rw [Category.assoc, Over.w f]
  exact hs

include B hB s hs in
omit [SmoothOfRelativeDimension g Y.hom] in
theorem projective_bijective :
    Function.Bijective (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R Y X f U₀ g) := by
  apply bijective_of_traces (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R Y X f U₀ g)
    (Intrinsic.TopFormTrace.traceIso X i B hB g (s ≫ f.left) (section_over X Y f s hs))
    (Intrinsic.EtaleProperTraceBase.IntrinsicFinite.traceIso X Y f i B hB g s hs)
  intro x
  exact (Intrinsic.TopFormTrace.traceIso_apply X i B hB g (s ≫ f.left)
    (section_over X Y f s hs) _).trans
      ((Intrinsic.FiniteEtaleProperTrace.trace_transfer X Y f i B hB g x).trans
        (Intrinsic.EtaleProperTraceBase.IntrinsicFinite.traceIso_apply X Y f i B hB g s hs x).symm)

variable [X.left.IsSeparated] {ι : Type u} (U : ι → X.left.Opens)
  (hU : ⨆ j, U j = ⊤) (haU : ∀ j, IsAffineOpen (U j)) (hg : 0 < g)

include i B hB s hs hU haU hg in
omit [SmoothOfRelativeDimension g Y.hom] in
theorem bijective : Function.Bijective (IntrinsicDeRham.TopEdgeTransfer.Intrinsic.trace R Y X f U g) := by
  let : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g).IsQuasicoherent :=
    IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R X g
  let : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g).IsQuasicoherent :=
    IntegralComparison.Smooth.FormCoherence.Integral.quasicoherent R Y g
  let : ((Scheme.Modules.pushforward f.left).obj (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y g)).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left
  have h₀ := (Intrinsic.ModuleTraceBijective.iff R Y X f U₀ g).mp
    (projective_bijective X Y f i B hB g s hs)
  have h₁ := ModuleCech.PositiveNaturality.bijective R X U₀ U
    (Intrinsic.TopFormTrace.cover_top X i) hU (Intrinsic.TopFormTrace.cover_affine X i) haU
    (ModuleTrace.trace R Y X f g) g hg h₀
  exact (Intrinsic.ModuleTraceBijective.iff R Y X f U g).mpr h₁

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.IntrinsicTraceBijective.Intrinsic
