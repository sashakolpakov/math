import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.OpenFunctionTranslationValues

/-! # Structure Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureCoordinates

noncomputable section

/-! The actual constant-torsor sheaf action becomes the regular representation on the sections over every base open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (G : Type u) [Group G]

theorem constantStructureRepresentation_coordinates (a : G) (U : S.Opens)
    (s : Γ((ConstantScheme.Iff.constantScheme S G).left, (ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U)) (i : G) :
    (ConstantScheme.OpenFunctions.constantSchemeOpenRingIso S G U).hom ((StructureRepresentation.constantStructureRepresentation S G a).app U s) i =
      (ConstantScheme.OpenFunctions.constantSchemeOpenRingIso S G U).hom s (i * a) :=
  (congrArg (fun z => (ConstantScheme.OpenFunctions.constantSchemeOpenRingIso S G U).hom z i)
    (StructureRepresentation.constantStructureRepresentation_app S G a U s)).trans
      (OpenFunctionTranslationValues.constantSchemeOpenRingIso_translate S G U a s i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureCoordinates
