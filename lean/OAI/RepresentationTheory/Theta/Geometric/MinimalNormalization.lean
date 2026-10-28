import OAI.RepresentationTheory.Theta.Geometric.NormalizationUnit
import OAI.RepresentationTheory.Theta.Geometric.Local.ClosedPointScalars
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification

/-! # Minimal Normalization -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalNormalization

noncomputable section

/-! The rank-one module and its unit axis normalization are derived from
the actual trivial closed fiber of a proper constant family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
    (π : X ⟶ S) (q : X ⟶ A) (t : S ⟶ Spec (.of K))
    (hX : IsPullback q π a t) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    {I : Type u} [LinearOrder I] [Finite I] (U : I → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ (n : ℕ) (i : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I n), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U)
    (hφ : ∀ (V : Type u) [AddCommGroup V] [Module Γ(S, ⊤) V],
      QuasiIso (AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map V φ))
    (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2))
    (i : I) (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    (eM : (Scheme.Modules.pullback (π.fiberι (Local.AxisCechChart.affineLocalClosedPoint S))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (Local.AxisCechChart.affineLocalClosedPoint S)))

include hX hU ha hφ eM in
theorem exists_geometric_minimal_normalization :
    ∃ e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁,
      IsUnit (MinimalNormalizedSections.minimalSectionFunctional P (ModelAxisNormalization.modelAxisFunctional s π hs L.sheaf U r i hi φ) (e 1)) := by
  let x := Local.AxisCechChart.affineLocalClosedPoint S
  let f := π.fiberι x
  let ρ := π.fiberToSpecResidueField x
  let g := S.fromSpecResidueField x
  have hp : IsPullback f ρ π g := IsPullback.of_hasPullback π g
  let b := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs
  have hb := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π g hp s hs
  have hx := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs
  have : IsLocalHom g.appTop.hom := Local.ClosedPointScalars.affineLocalResidue_isLocalHom S
  have : IsIso ρ.appTop := AlgebraicGeometry.Quotients.FiniteDescent.CartesianProductIs.Construction.CartesianProductFunctions.isIso_app a (f ≫ q) ρ (g ≫ t)
    (hp.paste_horiz hX) ⊤
  have : L.sheaf.IsQuasicoherent := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have := AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ g L.sheaf U φ hp ha hφ
  have hfield : IsField Γ(Spec (S.residueField x), ⊤) := by
    let : Field Γ(Spec (S.residueField x), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField (S.residueField x)
    exact Field.toIsField _
  have hdim := NormalizationUnit.minimal_first_finrank_of_trivial_geometric_fiber f g π ρ hp.w L.sheaf U φ hU P hfield eM
  let e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁ :=
    LinearEquiv.ofFinrankEq _ _ ((Module.finrank_self _).trans hdim.symm)
  exact ⟨e, NormalizationUnit.modelNormalization_unit_of_trivial_fiber f b g s hx π ρ hp.w hs hb
    L.sheaf U r i hi φ hU P e eM⟩

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalNormalization
