import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
import Mathlib.AlgebraicGeometry.Sites.Small

/-! # Open Cover Equality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.OpenCoverEquality

noncomputable section

/-! Equality in the actual relative Picard sheaf can be checked on an
arbitrary open cover of the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

def coverOverObject {S : Scheme.{u}} (T : Over S) (U : Scheme.OpenCover.{u} T.left) (i : U.I₀) : Over S :=
  Over.mk (U.f i ≫ T.hom)

def coverOverMap {S : Scheme.{u}} (T : Over S) (U : Scheme.OpenCover.{u} T.left) (i : U.I₀) :
    coverOverObject T U i ⟶ T := Over.homMk (U.f i)

theorem openCoverOverSieve_mem {S : Scheme.{u}} (T : Over S) (U : Scheme.OpenCover.{u} T.left) :
    Sieve.ofArrows (coverOverObject T U) (coverOverMap T U) ∈ (Scheme.fppfTopology.over S) T := by
  let (i : U.I₀) : (U.X i).Over S := ⟨U.f i ≫ T.hom⟩
  let : U.Over S := { isOver_map i := ⟨rfl⟩ }
  rw [GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv T (Sieve.generate U.toPresieveOver) ∈ Scheme.fppfTopology T.left
  rw [U.overEquiv_generate_toPresieveOver_eq_ofArrows]
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _ U.mem_grothendieckTopology

theorem fppfSheaf_eq_of_openCover {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) (T : Over S) (U : Scheme.OpenCover.{u} T.left)
    (x y : F.obj.obj (.op T))
    (h : ∀ i, F.obj.map (coverOverMap T U i).op x = F.obj.map (coverOverMap T U i).op y) : x = y := by
  have H : (TypeCat.ofHom (fun _ : PUnit.{u + 2} => x)) =
      TypeCat.ofHom (fun _ : PUnit.{u + 2} => y) := by
    apply F.property.hom_ext_ofArrows (coverOverMap T U) (openCoverOverSieve_mem T U)
    intro i
    ext t
    exact h i
  exact congrArg (fun f => f PUnit.unit) H

theorem relativePicard_eq_of_openCover {S : Scheme.{u}} (A T : Over S) (U : Scheme.OpenCover.{u} T.left)
    (q r : OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left)
    (h : ∀ i, OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((coverOverMap T U i) ⊗ₘ 𝟙 A).left q =
      OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((coverOverMap T U i) ⊗ₘ 𝟙 A).left r) :
    (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) q = (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) r := by
  apply fppfSheaf_eq_of_openCover (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A) T U
  intro i
  exact (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A (coverOverMap T U i) q).trans
    ((congrArg ((OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op (coverOverObject T U i))) (h i)).trans
      (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A (coverOverMap T U i) r).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.OpenCoverEquality
