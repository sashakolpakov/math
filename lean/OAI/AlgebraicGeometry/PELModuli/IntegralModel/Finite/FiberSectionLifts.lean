import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatSectionBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.GlobalSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.SectionGenerators

/-! # Fiber Section Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberSectionLifts

noncomputable section

/-! Finitely many actual global sections span all sections on a fiber
whose first cohomology vanishes. The family is extracted from finite
generation over the original affine base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

theorem properFlat_exists_finite_fiber_section_lifts
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : S)
    [Subsingleton (SheafCohomology.AffineH.Projective.H ((Scheme.Modules.pullback (f.fiberι x)).obj L.sheaf) 1)] :
    ∃ (n : ℕ) (s : Fin n → (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤)),
      Submodule.span Γ(Spec (S.residueField x), ⊤)
        (Set.range (fun i => (show (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (f.fiberToSpecResidueField x)
          ((Scheme.Modules.pullback (f.fiberι x)).obj L.sheaf)).obj (op ⊤) from
            CechPullbackSectionNormalization.pullbackTopSection (f.fiberι x) L.sheaf (s i)))) = ⊤ := by
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFiniteType := by
    let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  have : Module.Finite Γ(S, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤)) :=
    Proper.GlobalSections.proper_coherent_baseModuleTop_finite f L.sheaf
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(S, ⊤))
    (M := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤))
  obtain ⟨b, hb, hbone⟩ := Proper.FlatSectionBaseChange.properFlat_exists_surjective_fiber_section_map f L x
  refine ⟨n, s, ?_⟩
  simpa only [hbone] using Scalar.SectionGenerators.scalar_images_span_of_surjective
    (S.fromSpecResidueField x).appTop.hom _ _ b hb s hs

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberSectionLifts
