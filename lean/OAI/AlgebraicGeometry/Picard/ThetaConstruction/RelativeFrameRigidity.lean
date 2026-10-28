import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameMonomorphism

/-! # Relative Frame Rigidity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameRigidity.Geometric

noncomputable section

/-! Normalized frames on an actual smooth projective family are unique
after every base change. Global functions are derived from the original
projective presentation over its locally Noetherian base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : Over S} [IsProper X.hom] [Smooth X.hom] [GeometricallyConnected X.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S)

include P hs

theorem relativeProjective_frameAxisScalar_injective
    {Y T : Scheme.{u}} (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S)
    (hp : IsPullback f ρ X.hom g) (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T)
    (h : b ≫ f = g ≫ s) (M : X.left.Modules)
    (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    Function.Injective (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h M r) := by
  let : IsIso ρ.appTop := AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions.projectivePresentation_baseChange_globalFunctions_isIso P s hs hp
  let : IsIso b.appTop := FormalGeometry.Completion.Frame.AxisRigidity.Construction.section_appTop_isIso ρ b hb
  exact FormalGeometry.Completion.Frame.AxisRigidity.Construction.frameAxisScalar_injective f b g s h M r (ConcreteCategory.bijective_of_isIso b.appTop).1

variable [IsAffine S] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left}
    (D : FormalGeometry.Completion.Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation X.hom L.sheaf)
    (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

theorem relativeProjective_rigidifiedFrame_affinePoints_subsingleton
    (T : Over S) [IsAffine T.left] :
    Subsingleton (T ⟶ D.rigidifiedFrameScheme s hs r) := by
  let f := pullback.fst X.hom T.hom
  let ρ := pullback.snd X.hom T.hom
  let hp : IsPullback f ρ X.hom T.hom := IsPullback.of_hasPullback X.hom T.hom
  let b := FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection f ρ X.hom T.hom hp s hs
  let E := D.rigidifiedTrivializationPointEquiv f ρ T.hom hp s hs r
  refine ⟨fun v w => E.symm.injective ?_⟩
  apply Subtype.ext
  exact relativeProjective_frameAxisScalar_injective P s hs f ρ T.hom hp b
    (FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_snd f ρ X.hom T.hom hp s hs)
    (FormalGeometry.Completion.NormalizedFrameClassification.Construction.cartesianSection_fst f ρ X.hom T.hom hp s hs) L.sheaf r
    ((E.symm v).property.trans (E.symm w).property.symm)

theorem relativeProjective_rigidifiedFrame_mono : Mono (D.rigidifiedFrameScheme s hs r).hom := by
  constructor
  intro Z v w hvw
  apply Z.affineCover.hom_ext v w
  intro i
  let g := (Z.affineCover.f i ≫ v) ≫ (D.rigidifiedFrameScheme s hs r).hom
  let v' : Over.mk g ⟶ D.rigidifiedFrameScheme s hs r := Over.homMk (Z.affineCover.f i ≫ v) rfl
  let w' : Over.mk g ⟶ D.rigidifiedFrameScheme s hs r := Over.homMk (Z.affineCover.f i ≫ w) (by
    change (Z.affineCover.f i ≫ w) ≫ (D.rigidifiedFrameScheme s hs r).hom =
      (Z.affineCover.f i ≫ v) ≫ (D.rigidifiedFrameScheme s hs r).hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => Z.affineCover.f i ≫ z) hvw.symm).trans (Category.assoc _ _ _).symm))
  let : IsAffine (Over.mk g).left := inferInstanceAs (IsAffine (Z.affineCover.X i))
  let := relativeProjective_rigidifiedFrame_affinePoints_subsingleton P s hs D r (Over.mk g)
  exact congrArg Over.Hom.left (Subsingleton.elim v' w')

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameRigidity.Geometric
