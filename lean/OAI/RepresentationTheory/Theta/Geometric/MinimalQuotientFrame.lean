import OAI.RepresentationTheory.Theta.Geometric.MinimalQuotientGeometry
import OAI.RepresentationTheory.Theta.Geometric.Normalized.SectionEquations
import OAI.RepresentationTheory.Theta.Geometric.Local.BaseChangeFrames
import OAI.RepresentationTheory.Theta.Geometric.SectionAxisBaseChange

/-! # Minimal Quotient Frame -/

namespace OAI.RepresentationTheory.Theta.Geometric.MinimalQuotientFrame

noncomputable section

/-! The actual minimal-equation quotient carries a normalized frame.
The frame condition follows from its original trivial closed fiber and
properness of the constant family. -/

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
theorem minimalQuotient_hasNormalizedFrame
    (D : AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf) :
    Nonempty (Affine.QuotientPoints.affineQuotientScheme S (MinimalEquationIdeal.minimalEquationIdeal P basis e) ⟶
      D.rigidifiedFrameScheme s hs r) := by
  let Q := Affine.QuotientPoints.affineQuotientScheme S (MinimalEquationIdeal.minimalEquationIdeal P basis e)
  let f := pullback.fst π Q.hom
  let ρ := pullback.snd π Q.hom
  have hp : IsPullback f ρ π Q.hom := IsPullback.of_hasPullback π Q.hom
  let b := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ π Q.hom hp s hs
  have hb := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π Q.hom hp s hs
  have hx := AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π Q.hom hp s hs
  have : IsAffine Q.left := inferInstanceAs (IsAffine (Spec (.of (Γ(S, ⊤) ⧸ MinimalEquationIdeal.minimalEquationIdeal P basis e))))
  have : L.sheaf.IsQuasicoherent := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have := AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap_quasiIso f π ρ Q.hom L.sheaf U φ hp ha hφ
  have hkill : MinimalEquationIdeal.minimalEquationIdeal P basis e ≤ RingHom.ker Q.hom.appTop.hom :=
    (Affine.QuotientPoints.affineQuotientScheme_hasLift_iff S (MinimalEquationIdeal.minimalEquationIdeal P basis e) Q).mp ⟨𝟙 Q⟩
  obtain ⟨z, hz⟩ := (Normalized.SectionEquations.normalized_geometric_sections_equations f b Q.hom s hx π ρ hp.w hs hb
    L.sheaf U r i hi φ hU P basis e hu).mpr hkill
  let v := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf)).symm z
  have hv : (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b Q.hom s hx L.sheaf r).hom.app ⊤
      (AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionCechPullback.Construction.globalLineSectionPullback b ((Scheme.Modules.pullback f).obj L.sheaf)
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ v)) = (1 : Γ(Q.left, ⊤)) := by
    simpa only [v, Equiv.apply_symm_apply] using hz
  have ef : (Scheme.Modules.pullback (π.fiberι
      (Q.hom (IsLocalRing.closedPoint (Γ(S, ⊤) ⧸ MinimalEquationIdeal.minimalEquationIdeal P basis e))))).obj L.sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π.fiber
        (Q.hom (IsLocalRing.closedPoint (Γ(S, ⊤) ⧸ MinimalEquationIdeal.minimalEquationIdeal P basis e)))) := by
    change (Scheme.Modules.pullback (π.fiberι ((Affine.QuotientPoints.affineQuotientScheme S
      (MinimalEquationIdeal.minimalEquationIdeal P basis e)).hom (IsLocalRing.closedPoint _)))).obj L.sheaf ≅ _
    rw [MinimalQuotientGeometry.minimalQuotient_closedPoint]
    exact eM
  have : IsIso v := Local.BaseChangeFrames.localBaseChange_normalizedSection_isIso a π q t hX f ρ Q.hom hp
    s b hb hx L r v hv ef
  refine ⟨D.normalizedTrivializationPointEquiv f ρ Q.hom hp s hs b hb hx r ⟨asIso v, ?_⟩⟩
  have he := Normalized.ClosedFiberFrames.rigidifiedSection_endValue b ((Scheme.Modules.pullback f).obj L.sheaf)
    (AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f b Q.hom s hx L.sheaf r) v
  exact (SectionAxisBaseChange.sectionAxisScalar_frame f b Q.hom s hx L.sheaf r (asIso v)).symm.trans (he.trans hv)

end

end OAI.RepresentationTheory.Theta.Geometric.MinimalQuotientFrame
