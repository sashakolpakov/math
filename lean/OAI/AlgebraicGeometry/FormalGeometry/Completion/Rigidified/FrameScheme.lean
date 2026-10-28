import OAI.AlgebraicGeometry.FormalGeometry.Completion.UniversalRigidificationScalar
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarEquationFamilyPoints

/-! # Frame Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The universal frame's value-one equation gives an actual closed
subscheme of the frame scheme, locally of finite type and of finite
type over a Noetherian base. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
  (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrameScheme : Over S :=
  ScalarEquationFamilyPoints.Construction.scalarEqOneFamily D.frameSchemeOverBase (D.rigidificationScalar s hs r)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrameInclusion : D.rigidifiedFrameScheme s hs r ⟶ D.frameSchemeOverBase :=
  ScalarEquationFamilyPoints.Construction.scalarEqOneFamilyInclusion D.frameSchemeOverBase (D.rigidificationScalar s hs r)

instance Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrameInclusion_isClosedImmersion :
    IsClosedImmersion (D.rigidifiedFrameInclusion s hs r).left :=
  inferInstanceAs (IsClosedImmersion
    (ScalarEquationFamilyPoints.Construction.scalarEqOneFamilyInclusion D.frameSchemeOverBase (D.rigidificationScalar s hs r)).left)

instance Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrameScheme_locallyOfFiniteType :
    LocallyOfFiniteType (D.rigidifiedFrameScheme s hs r).hom := by
  change LocallyOfFiniteType ((GlobalScalarEquation.Construction.scalarEqOneScheme D.frameSchemeOverBase.left
    (D.rigidificationScalar s hs r)).hom ≫ D.frameSchemeOverBase.hom)
  infer_instance

instance Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrameScheme_quasiCompact [IsNoetherianRing Γ(S, ⊤)] :
    QuasiCompact (D.rigidifiedFrameScheme s hs r).hom := by
  change QuasiCompact ((GlobalScalarEquation.Construction.scalarEqOneScheme D.frameSchemeOverBase.left
    (D.rigidificationScalar s hs r)).hom ≫ D.frameSchemeOverBase.hom)
  infer_instance

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFramePointEquiv (T : Over S) :
    (T ⟶ D.rigidifiedFrameScheme s hs r) ≃
      { p : T ⟶ D.frameSchemeOverBase // p.left.appTop (D.rigidificationScalar s hs r) = 1 } :=
  ScalarEquationFamilyPoints.Construction.scalarEqOneFamilyPointEquiv D.frameSchemeOverBase (D.rigidificationScalar s hs r) T

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrameInclusion_scalar :
    (D.rigidifiedFrameInclusion s hs r).left.appTop (D.rigidificationScalar s hs r) = 1 :=
  (GlobalScalarEquation.Construction.scalarEqOneScheme_hasLift_iff (D.rigidificationScalar s hs r)
    (GlobalScalarEquation.Construction.scalarEqOneScheme D.frameSchemeOverBase.left (D.rigidificationScalar s hs r)).hom).mp ⟨𝟙 _⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
