import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.FrameScalar

/-! # Universal Rigidification Scalar -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The frame scheme has a concrete invertible function measuring the
value of its universal frame on a prescribed rigidification axis. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameAxis : D.frameSchemeOverBase.left ⟶ D.frameFamily :=
  D.frameFamily_isPullback.lift (D.frameSchemeOverBase.hom ≫ s) (𝟙 _) (by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameAxis_fst : D.frameAxis s hs ≫ D.frameFamilyToOriginal = D.frameSchemeOverBase.hom ≫ s :=
  D.frameFamily_isPullback.lift_fst _ _ _

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameAxis_snd : D.frameAxis s hs ≫ D.frameFamilyProjection = 𝟙 _ :=
  D.frameFamily_isPullback.lift_snd _ _ _

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidificationScalar (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    Γ(D.frameSchemeOverBase.left, ⊤) :=
  Rigidified.FrameScalar.Construction.frameAxisScalar D.frameFamilyToOriginal (D.frameAxis s hs) D.frameSchemeOverBase.hom s
    (D.frameAxis_fst s hs) L.sheaf r D.tautologicalFrame

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidificationScalar_isUnit (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) :
    IsUnit (D.rigidificationScalar s hs r) :=
  Rigidified.FrameScalar.Construction.frameAxisScalar_isUnit D.frameFamilyToOriginal (D.frameAxis s hs) D.frameSchemeOverBase.hom s
    (D.frameAxis_fst s hs) L.sheaf r D.tautologicalFrame

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
