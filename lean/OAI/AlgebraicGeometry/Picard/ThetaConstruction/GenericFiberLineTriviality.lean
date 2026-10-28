import OAI.AlgebraicGeometry.Picard.ThetaConstruction.FiberSectionSpecialization
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReducedLocalFiberTriviality
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionPair
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothGeometricIntegrality
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup

/-! # Generic Fiber Line Triviality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericFiberLineTriviality.Geometric

noncomputable section

/-! Triviality of a line on a smooth proper geometrically connected
fiber persists under specialization: both it and its inverse retain
nonzero sections. A normalized generically trivial line over an
integral local base is consequently trivial on the whole family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup.Construction OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionPair.Construction.SectionPairTriviality

universe u
variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)

theorem fiberLine_trivial_specializes {x y : S} (hxy : x ⤳ y)
    (hx : Nonempty ((L.pullback (f.fiberι x)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f.fiber x))) :
    Nonempty ((L.pullback (f.fiberι y)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f.fiber y)) := by
  let M := Homomorphisms.LineBundleDual.Construction.lineBundleDual L
  have hpair (z : S) : Nonempty
      (((L.pullback (f.fiberι z)).tensor (M.pullback (f.fiberι z))).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f.fiber z)) := by
    exact ⟨(AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso (f.fiberι z) L M).symm ≪≫
      (Scheme.Modules.pullback (f.fiberι z)).mapIso
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso L.sheaf M.sheaf ≪≫ Homomorphisms.LineBundleEvaluation.Construction.lineBundleEvaluationIso L) ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f.fiberι z)⟩
  let (z : S) : IsProper (f.fiberToSpecResidueField z) :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField z)))
  let (z : S) : Smooth (f.fiberToSpecResidueField z) :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField z)))
  let (z : S) : GeometricallyConnected (f.fiberToSpecResidueField z) :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField z)))
  let hproperX : IsProper (Over.mk (f.fiberToSpecResidueField x)).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField x)))
  let hproperY : IsProper (Over.mk (f.fiberToSpecResidueField y)).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField y)))
  have (z : S) : GeometricallyIntegral (f.fiberToSpecResidueField z) :=
    FormalGeometry.Completion.SmoothGeometricIntegrality.Construction.proper_smooth_geometricallyIntegral_of_geometricallyConnected _
  have hIntegral (z : S) : IsIntegral (f.fiber z) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (f.fiberToSpecResidueField z)
  have hp := (@Quotients.FiniteDescent.SectionPair.Construction.SectionPairTriviality.pair_iff (S.residueField x) _ (Over.mk (f.fiberToSpecResidueField x))
    hproperX (hIntegral x)
    (L.pullback (f.fiberι x)) (M.pullback (f.fiberι x)) (Classical.choice (hpair x))).mp hx
  have hsectionsL := FiberSectionSpecialization.Geometric.fiberSections_nontrivial_specializes f L hxy hp.1
  have hsectionsM := FiberSectionSpecialization.Geometric.fiberSections_nontrivial_specializes f M hxy hp.2
  exact @Quotients.FiniteDescent.SectionPair.Construction.SectionPairTriviality.trivial_of_sections (S.residueField y) _ (Over.mk (f.fiberToSpecResidueField y))
    hproperY (hIntegral y) (L.pullback (f.fiberι y)) (M.pullback (f.fiberι y))
    (Classical.choice (hpair y)) hsectionsL hsectionsM

theorem genericFiber_line_trivial [IsLocalRing Γ(S, ⊤)] [IsLocallyNoetherian S]
    [IsReduced S] [IrreducibleSpace S]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (hη : Nonempty ((L.pullback (f.fiberι (genericPoint S))).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f.fiber (genericPoint S)))) :
    Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
  let : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  let : Smooth (Over.mk f).hom := inferInstanceAs (Smooth f)
  let : GeometricallyConnected (Over.mk f).hom := inferInstanceAs (GeometricallyConnected f)
  apply ReducedLocalFiberTriviality.Geometric.reducedLocal_line_trivial P s hs L r
  intro y
  exact fiberLine_trivial_specializes f L (genericPoint_specializes y) hη

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericFiberLineTriviality.Geometric
