import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness

/-! # Normalized Squares -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares

noncomputable section

/-! Compatibility of normalized line-bundle isomorphisms with actual
commutative squares of schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf.PicardModuleHomSheaf

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness

variable {X X' T T' : Scheme.{u}}
variable (g : X' ⟶ X) (z : T ⟶ X) (z' : T' ⟶ X') (t : T' ⟶ T)
variable (h : z' ≫ g = t ≫ z)

def sectionSquareIso :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback z' ≅
      Scheme.Modules.pullback z ⋙ Scheme.Modules.pullback t :=
  Scheme.Modules.pullbackComp z' g ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp t z).symm

/-- The zero trivialization transported through the given square. -/
def squareZeroIso {M : X.Modules}
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T) :
    (Scheme.Modules.pullback z').obj ((Scheme.Modules.pullback g).obj M) ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T' :=
  (sectionSquareIso g z z' t h).app M ≪≫
    (Scheme.Modules.pullback t).mapIso eM ≪≫ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso t

/-- Naturality of the actual pullback-composition maps transports the
normalization equation, without choosing another zero trivialization. -/
theorem pullback_preserves_normalization {M N : X.Modules} (e : M ≅ N)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (he : (Scheme.Modules.pullback z).map e.hom ≫ eN.hom = eM.hom) :
    (Scheme.Modules.pullback z').map ((Scheme.Modules.pullback g).map e.hom) ≫
      (squareZeroIso g z z' t h eN).hom = (squareZeroIso g z z' t h eM).hom := by
  let α := sectionSquareIso g z z' t h
  let L := Scheme.Modules.pullback t
  change (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback z').map e.hom ≫
    (α.hom.app N ≫ L.map eN.hom ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso t).hom) =
      α.hom.app M ≫ L.map eM.hom ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso t).hom
  rw [← Category.assoc, α.hom.naturality, Category.assoc, ← Category.assoc
    ((Scheme.Modules.pullback z ⋙ L).map e.hom), Functor.comp_map, ← L.map_comp, he]

/-- Normalizing and then pulling back gives the same isomorphism as
pulling back and normalizing with the transported trivializations. -/
theorem normalizedIso_pullback (π : X ⟶ T) (π' : X' ⟶ T')
    (hπ : z ≫ π = 𝟙 T) (hπ' : z' ≫ π' = 𝟙 T')
    (hΓ' : Function.Surjective π'.appTop)
    {M N : X.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (e : M ≅ N)
    (eM : (Scheme.Modules.pullback z).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T)
    (eN : (Scheme.Modules.pullback z).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule T) :
    Isogenies.NeighborCounting.RigidifiedIso.normalizedIso π' z' ((Scheme.Modules.pullback g).mapIso e)
        (squareZeroIso g z z' t h eM) (squareZeroIso g z z' t h eN) =
      (Scheme.Modules.pullback g).mapIso (Isogenies.NeighborCounting.RigidifiedIso.normalizedIso π z e eM eN) := by
  apply RigidifiedUniqueness.PicardRigidifiedUniqueness.normalizedIso_unique π' z' hπ' hΓ' (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.isLineBundle_pullback g M hM)
    (squareZeroIso g z z' t h eM) (squareZeroIso g z z' t h eN)
  · exact Isogenies.NeighborCounting.RigidifiedIso.normalizedIso_section π' z' hπ' _ _ _
  · exact pullback_preserves_normalization g z z' t h _ eM eN
      (Isogenies.NeighborCounting.RigidifiedIso.normalizedIso_section π z hπ e eM eN)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.NormalizedSquares.PicardNormalizedSquares
