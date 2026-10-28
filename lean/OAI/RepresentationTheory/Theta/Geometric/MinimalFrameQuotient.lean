import OAI.RepresentationTheory.Theta.Geometric.MinimalQuotientFrame
import OAI.RepresentationTheory.Theta.Geometric.NormalizationUnit
import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMonomorphisms
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameMonomorphism

/-! # Minimal Frame Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalFrameQuotient

noncomputable section

/-! The actual normalized-frame scheme over a local affine base is the
closed quotient by the original minimal differential coefficients. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
    (π : X ⟶ S) [IsProper π] (q : X ⟶ A) (t : S ⟶ Spec (.of K))
    (hX : IsPullback q π a t) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    {I : Type u} [LinearOrder I] [Finite I] (U : I → X.Opens) (hU : iSup U = ⊤)
    (ha : ∀ (n : ℕ) (i : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex I n), IsAffineOpen (∏ᶜ fun k => U (i.1 k)))
    {C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
    (φ : C ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U)
    (hφ : ∀ (V : Type u) [AddCommGroup V] [Module Γ(S, ⊤) V],
      QuasiIso (AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map V φ))
    (P : AlgebraicGeometry.Quotients.FiniteDescent.LocalMinimalShort.Construction.LocalSectionLifting.LocalMinimalShortComplex (C.sc' 0 1 2)) {J : Type*}
    (basis : Module.Basis J Γ(S, ⊤) P.complex.X₂)
    (e : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] P.complex.X₁)
    (i : I) (hi : (⊤ : S.Opens) ≤ s ⁻¹ᵁ AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.intersection U 0
      (AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechEq.Construction.OrderedCechZeroCoordinates.single i))
    (hu : IsUnit (MinimalNormalizedSections.minimalSectionFunctional P (ModelAxisNormalization.modelAxisFunctional s π hs L.sheaf U r i hi φ) (e 1)))
    (eM : (Scheme.Modules.pullback (π.fiberι (Local.AxisCechChart.affineLocalClosedPoint S))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber (Local.AxisCechChart.affineLocalClosedPoint S)))

include hX hU ha hφ hu eM in
theorem minimalFrame_hasLift_iff
    (D : AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
    (T : Over S) [IsAffine T.left] :
    Nonempty (T ⟶ D.rigidifiedFrameScheme s hs r) ↔
      MinimalEquationIdeal.minimalEquationIdeal P basis e ≤ RingHom.ker T.hom.appTop.hom := by
  constructor
  · rintro ⟨p⟩
    let f := pullback.fst π T.hom
    let ρ := pullback.snd π T.hom
    have hp : IsPullback f ρ π T.hom := IsPullback.of_hasPullback π T.hom
    let b := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ π T.hom hp s hs
    have hb := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π T.hom hp s hs
    have hx := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π T.hom hp s hs
    have : L.sheaf.IsQuasicoherent := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
    have := AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ T.hom L.sheaf U φ hp ha hφ
    let v := (D.normalizedTrivializationPointEquiv f ρ T.hom hp s hs b hb hx r).symm p
    have hn := NormalizationUnit.trivialization_exists_normalizedSection f ρ b hb T.hom s hx L.sheaf r v.val.symm
    exact (Normalized.SectionEquations.normalized_geometric_sections_equations f b T.hom s hx π ρ hp.w hs hb
      L.sheaf U r i hi φ hU P basis e hu).mp hn
  · intro h
    obtain ⟨p⟩ := (Affine.QuotientPoints.affineQuotientScheme_hasLift_iff S (MinimalEquationIdeal.minimalEquationIdeal P basis e) T).mpr h
    obtain ⟨v⟩ := MinimalQuotientFrame.minimalQuotient_hasNormalizedFrame a π q t hX s hs L r U hU ha φ hφ
      P basis e i hi hu eM D
    exact ⟨p ≫ v⟩

include hX hU ha hφ hu eM in
def minimalFrameQuotientIso
    (D : AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf) :
    D.rigidifiedFrameScheme s hs r ≅ Affine.QuotientPoints.affineQuotientScheme S (MinimalEquationIdeal.minimalEquationIdeal P basis e) := by
  have : Mono (D.rigidifiedFrameScheme s hs r).hom := D.rigidifiedFrame_mono a q t hX s hs r
  exact Affine.TestMonomorphisms.monoAffineQuotientIso (D.rigidifiedFrameScheme s hs r) (MinimalEquationIdeal.minimalEquationIdeal P basis e)
    (fun T _ => minimalFrame_hasLift_iff a π q t hX s hs L r U hU ha φ hφ P basis e i hi hu eM D T)

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalFrameQuotient
