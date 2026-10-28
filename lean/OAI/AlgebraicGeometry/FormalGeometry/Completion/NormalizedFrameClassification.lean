import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClassifiedRigidificationScalar
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScheme

/-! # Normalized Frame Classification -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The closed rigidified-frame scheme classifies actual trivializations
with value one along the specified section. The axis on each Cartesian
test family is derived from the universal property of the pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

def NormalizedFrameClassification.Construction.cartesianSection {X Y S T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (π : X ⟶ S) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S) : T ⟶ Y :=
  hp.lift (g ≫ s) (𝟙 T) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

theorem NormalizedFrameClassification.Construction.cartesianSection_fst {X Y S T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (π : X ⟶ S) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S) :
    NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs ≫ f = g ≫ s := hp.lift_fst _ _ _

theorem NormalizedFrameClassification.Construction.cartesianSection_snd {X Y S T : Scheme.{u}} (f : Y ⟶ X) (ρ : Y ⟶ T) (π : X ⟶ S) (g : T ⟶ S)
    (hp : IsPullback f ρ π g) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S) :
    NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs ≫ ρ = 𝟙 T := hp.lift_snd _ _ _

variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  {Y T : Scheme.{u}} [IsAffine T] (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
  (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
  (b : T ⟶ Y) (hb : b ≫ ρ = 𝟙 T) (h : b ≫ f = g ≫ s)
  (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.normalizedTrivializationPointEquiv :
    { e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf // Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h L.sheaf r e = 1 } ≃
      (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) :=
  ((D.lineBundleTrivializationPointEquiv f ρ g hp).subtypeEquiv (fun e =>
    (congrArg (fun z : Γ(T, ⊤) => z = 1) (D.frameAxisScalar_classifier f ρ g hp s hs b hb h r e)).to_iff)).trans
      (D.rigidifiedFramePointEquiv s hs r (Over.mk g)).symm

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.normalizedTrivializationPointEquiv_inclusion
    (e : { e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf // Rigidified.FrameScalar.Construction.frameAxisScalar f b g s h L.sheaf r e = 1 }) :
    D.normalizedTrivializationPointEquiv f ρ g hp s hs b hb h r e ≫ D.rigidifiedFrameInclusion s hs r =
      D.lineBundleTrivializationPointEquiv f ρ g hp e.val :=
  ScalarEquationFamilyPoints.Construction.scalarEqOneFamilyLift_fac D.frameSchemeOverBase (D.rigidificationScalar s hs r) (Over.mk g)
    (D.lineBundleTrivializationPointEquiv f ρ g hp e.val)
      ((D.frameAxisScalar_classifier f ρ g hp s hs b hb h r e.val).symm.trans e.property)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedTrivializationPointEquiv :
    { e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf //
      Rigidified.FrameScalar.Construction.frameAxisScalar f (NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs) g s
        (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs) L.sheaf r e = 1 } ≃
      (Over.mk g ⟶ D.rigidifiedFrameScheme s hs r) :=
  D.normalizedTrivializationPointEquiv f ρ g hp s hs (NormalizedFrameClassification.Construction.cartesianSection f ρ π g hp s hs)
    (NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π g hp s hs) (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π g hp s hs) r

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
