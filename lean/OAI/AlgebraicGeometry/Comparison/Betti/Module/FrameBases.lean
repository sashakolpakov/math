import OAI.AlgebraicGeometry.Comparison.Betti.SheafificationBasis
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Frame Bases -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.FrameBases.Frames

noncomputable section

section

/-! Global sections define actual module frames, and a basis of local frames proves a sheaf isomorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0})
  (P : PresheafOfModules.{0} R.obj) {ι : Type} (b : ι → P.obj (op ⊤))

def restrictedGenerators : (Functor.const (Opens X)ᵒᵖ).obj ι ⟶ P.presheaf ⋙ forget AddCommGrpCat where
  app U := ↾fun i => P.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (b i)
  naturality U V f := by
    ext i
    change P.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op (b i) =
      P.map f (P.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (b i))
    exact P.map_comp_apply (homOfLE (show U.unop ≤ ⊤ from le_top)).op f (b i)

def frame : PresheafOfModules.freeObj (R := R.obj) ((Functor.const (Opens X)ᵒᵖ).obj ι) ⟶ P :=
  PresheafOfModules.freeObjDesc (restrictedGenerators R P b)

theorem frame_apply (U : (Opens X)ᵒᵖ) (i : ι) :
    (frame R P b).app U (ModuleCat.freeMk i) =
      P.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (b i) :=
  ModuleCat.freeDesc_apply ((restrictedGenerators R P b).app U) i

theorem sheafified_frame_isIso {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hb : ∀ U ∈ B, IsIso ((frame R P b).app (op U))) :
    IsIso ((PresheafOfModules.sheafification.{0} (R := R) (𝟙 R.obj)).map (frame R P b)) := by
  let a := (PresheafOfModules.toPresheaf R.obj).map (frame R P b)
  have ha : ∀ U ∈ B, IsIso (a.app (op U)) := by
    intro U hU
    have := hb U hU
    exact Functor.map_isIso (forget₂ (ModuleCat (R.obj.obj (op U))) AddCommGrpCat)
      ((frame R P b).app (op U))
  have : IsIso ((SheafOfModules.toSheaf.{0} R).map
      ((PresheafOfModules.sheafification.{0} (R := R) (𝟙 R.obj)).map (frame R P b))) :=
    SheafificationBasis.map_isIso a hB ha
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{0} R)

end

/-! Restricted sections that are actual bases make the constructed module frame invertible. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0})
  (P : PresheafOfModules.{0} R.obj) {ι : Type} (b : ι → P.obj (op ⊤))

theorem frame_app_isIso (U : (Opens X)ᵒᵖ) (c : Module.Basis ι (R.obj.obj U) (P.obj U))
    (hc : ∀ i, P.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (b i) = c i) :
    IsIso ((frame R P b).app U) := by
  let e : (ModuleCat.free (R.obj.obj U)).obj ι ≅ P.obj U := c.repr.symm.toModuleIso
  have he : (frame R P b).app U = e.hom := by
    apply ModuleCat.free_hom_ext
    intro i
    erw [frame_apply, hc]
    exact (c.repr_symm_single_one i).symm
  rw [he]
  change IsIso e.hom
  infer_instance

theorem sheafified_frame_isIso_of_bases {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (c : ∀ U ∈ B, Module.Basis ι (R.obj.obj (op U)) (P.obj (op U)))
    (hc : ∀ U hU i, P.map (homOfLE (show U ≤ ⊤ from le_top)).op (b i) = c U hU i) :
    IsIso ((PresheafOfModules.sheafification.{0} (R := R) (𝟙 R.obj)).map (frame R P b)) :=
  sheafified_frame_isIso R P b hB (fun U hU => frame_app_isIso R P b (op U) (c U hU) (hc U hU))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.FrameBases.Frames
