import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenCoefficients

/-! # Structure Section Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureSectionEquivalence

noncomputable section

/-! Over every open, the actual constant-torsor pushforward sections are linearly equivalent to the regular function module over the ring of that open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (G : Type u) [Group G] (U : S.Opens)

def constantStructureSectionEquiv :
    Γ(StructureRepresentation.constantStructurePushforward S G, U) ≃ₗ[Γ(S, U)] (G → Γ(S, U)) where
  __ := (ConstantScheme.OpenCoefficients.constantSchemeSectionRingEquiv S G U).toAddEquiv
  map_smul' r s := by
    change Γ((ConstantScheme.Iff.constantScheme S G).left, (ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U) at s
    change ConstantScheme.OpenCoefficients.constantSchemeSectionRingEquiv S G U ((ConstantScheme.Iff.constantScheme S G).hom.app U r * s) =
      r • ConstantScheme.OpenCoefficients.constantSchemeSectionRingEquiv S G U s
    rw [map_mul]
    funext i
    exact congrArg (fun z => z * ConstantScheme.OpenCoefficients.constantSchemeSectionRingEquiv S G U s i)
      (ConstantScheme.OpenCoefficients.constantSchemeSectionRingEquiv_structure S G U r i)

theorem constantStructureSectionEquiv_translate (a : G)
    (s : Γ(StructureRepresentation.constantStructurePushforward S G, U)) (i : G) :
    constantStructureSectionEquiv S G U ((StructureRepresentation.constantStructureRepresentation S G a).app U s) i =
      constantStructureSectionEquiv S G U s (i * a) :=
  congrArg (fun z => U.topIso.hom z) (StructureCoordinates.constantStructureRepresentation_coordinates S G a U s i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureSectionEquivalence
