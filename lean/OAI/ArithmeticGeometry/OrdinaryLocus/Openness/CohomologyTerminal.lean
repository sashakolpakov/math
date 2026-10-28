import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCohomologyOne

/-! # Cohomology Terminal -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTerminal.Construction

noncomputable section

/-! Comparison of local and global sheaf cohomology at a terminal object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Abelian

universe u v w

def freeAbelianUniqueIso (α : Type v) [Unique α] :
    AddCommGrpCat.free.obj α ≅ AddCommGrpCat.of (ULift.{v} ℤ) where
  hom := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ ↦ ULift.up 1)
  inv := AddCommGrpCat.ofHom (uliftZMultiplesHom _ (FreeAbelianGroup.of (default : α)))
  hom_inv_id := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro a
    change uliftZMultiplesHom _ (FreeAbelianGroup.of (default : α))
      (FreeAbelianGroup.lift (fun _ : α ↦ ULift.up 1) (FreeAbelianGroup.of a)) =
        FreeAbelianGroup.of a
    rw [FreeAbelianGroup.lift_apply_of, uliftZMultiplesHom_apply_apply]
    change (1 : ℤ) • FreeAbelianGroup.of (default : α) = FreeAbelianGroup.of a
    simp [Subsingleton.elim a default]
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    rintro ⟨n⟩
    change FreeAbelianGroup.lift (fun _ : α ↦ ULift.up 1)
      (uliftZMultiplesHom _ (FreeAbelianGroup.of (default : α)) (ULift.up n)) = ULift.up n
    rw [uliftZMultiplesHom_apply_apply, map_zsmul, FreeAbelianGroup.lift_apply_of]
    apply ULift.ext
    change n • (1 : ℤ) = n
    simp

variable {C : Type u} [Category.{v} C] {T : C} (hT : IsTerminal T)

def terminalFreeAbelianYonedaIso :
    yoneda.obj T ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) := by
  letI terminalHomUnique (Y : C) : Unique (Y ⟶ T) :=
    { default := hT.from Y, uniq := fun f ↦ hT.hom_ext f (hT.from Y) }
  refine NatIso.ofComponents (fun Y ↦ freeAbelianUniqueIso (Y.unop ⟶ T)) ?_
  intro Y Z f
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro g
  simp [freeAbelianUniqueIso, AddCommGrpCat.free, FreeAbelianGroup.map]

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

def terminalFreeAbelianSheafIso :
    (presheafToSheaf J AddCommGrpCat).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat).mapIso (terminalFreeAbelianYonedaIso hT)

variable [HasExt.{w} (CategoryTheory.Sheaf J AddCommGrpCat.{v})]

def cohomologyAtTerminalIso (F : CategoryTheory.Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    F.H' n T ≅ AddCommGrpCat.of (CategoryTheory.Sheaf.H F n) :=
  (((extFunctor n).mapIso (terminalFreeAbelianSheafIso hT J).op).app F).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTerminal.Construction
