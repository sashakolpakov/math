import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperAmbient
import OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersionDescent

/-! # Proper Cover -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCover.Construction

noncomputable section

/-! A proper model covering a reduced generic fiber gives a proper model
of that fiber by taking a schematic image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem proper_cover_gives_proper_model
    {S T : Scheme.{u}} (g : T ⟶ S)
    (P Y : Over S) [IsProper P.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (f : P ⟶ Y)
    [Surjective ((Over.pullback g).map f).left]
    [IsReduced ((Over.pullback g).obj Y).left] :
    ∃ M : Over S, IsProper M.hom ∧
      Nonempty ((Over.pullback g).obj M ≅ (Over.pullback g).obj Y) := by
  let M : Over S := Over.mk (f.left.imageι ≫ Y.hom)
  let j : M ⟶ Y := Over.homMk f.left.imageι rfl
  let a : P ⟶ M := Over.homMk f.left.toImage (by
    change f.left.toImage ≫ (f.left.imageι ≫ Y.hom) = P.hom
    rw [← Category.assoc, f.left.toImage_imageι, f.w])
  have haj : a ≫ j = f := by
    apply Over.OverMorphism.ext
    exact f.left.toImage_imageι
  let B := Over.pullback g
  have : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion f.left.imageι)
  have : IsClosedImmersion (B.map j).left := ClosedImmersionDescent.Construction.baseChange_closedImmersion g j
  have : Surjective ((B.map a).left ≫ (B.map j).left) := by
    change Surjective (B.map a ≫ B.map j).left
    rw [← B.map_comp, haj]
    infer_instance
  have : Surjective (B.map j).left := Surjective.of_comp (B.map a).left (B.map j).left
  have : IsIso (B.map j).left := isIso_of_isClosedImmersion_of_surjective (B.map j).left
  exact ⟨M, ProperAmbient.Construction.proper_schematic_image P Y f,
    ⟨Over.isoMk (asIso (B.map j).left) (B.map j).w⟩⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCover.Construction
