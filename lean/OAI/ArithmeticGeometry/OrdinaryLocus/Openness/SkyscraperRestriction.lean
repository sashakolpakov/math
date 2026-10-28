import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineLocalCohomology
import Mathlib.Topology.Sheaves.Over
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Skyscraper Restriction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SkyscraperRestriction.Construction

noncomputable section

/-! Restricting skyscraper sheaves to an open subspace. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} (U : Opens X) (x : X) (I : AddCommGrpCat.{u})

theorem openRestrictSkyscraper_obj (hx : x ∈ U) (V : Opens U) :
    (U.sheafRestrict.obj ((AbelianSheafInjectives.Construction.abelianSheafSkyscraper X x).obj I)).obj.obj (op V) =
      ((AbelianSheafInjectives.Construction.abelianSheafSkyscraper (TopCat.of U) ⟨x, hx⟩).obj I).obj.obj (op V) := by
  classical
  simp only [Opens.sheafRestrict_obj_obj_obj, AbelianSheafInjectives.Construction.abelianSheafSkyscraper,
    skyscraperSheafFunctor, skyscraperSheaf, skyscraperPresheaf_obj]
  congr 1
  change (x ∈ Subtype.val '' (V : Set U)) = ((⟨x, hx⟩ : U) ∈ V)
  apply propext
  constructor
  · rintro ⟨y, hy, heq⟩
    have : y = (⟨x, hx⟩ : U) := Subtype.ext heq
    exact this ▸ hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

def openRestrictSkyscraperIso (hx : x ∈ U) :
    U.sheafRestrict.obj ((AbelianSheafInjectives.Construction.abelianSheafSkyscraper X x).obj I) ≅
      (AbelianSheafInjectives.Construction.abelianSheafSkyscraper (TopCat.of U) ⟨x, hx⟩).obj I := by
  classical
  refine ObjectProperty.isoMk _ ?_
  refine NatIso.ofComponents (fun V ↦ eqToIso (openRestrictSkyscraper_obj U x I hx V.unop)) ?_
  intro V W f
  by_cases hW : (⟨x, hx⟩ : U) ∈ W.unop
  · have hV : (⟨x, hx⟩ : U) ∈ V.unop := f.unop.le hW
    have hW' : x ∈ Subtype.val '' (W.unop : Set U) := ⟨⟨x, hx⟩, hW, rfl⟩
    have hV' : x ∈ Subtype.val '' (V.unop : Set U) := ⟨⟨x, hx⟩, hV, rfl⟩
    simp [Opens.sheafRestrict_obj_obj_map, AbelianSheafInjectives.Construction.abelianSheafSkyscraper,
      skyscraperSheafFunctor, skyscraperSheaf, skyscraperPresheaf_map,
      IsOpenMap.functor, hW, hV, hW', hV', eqToIso]
    exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm
  · exact (isTerminalSkyscraperSheafObjObjOfNotMem
      (X := TopCat.of U) (A := I) (p₀ := (⟨x, hx⟩ : U)) (U := W) hW).hom_ext _ _

theorem openRestrictSkyscraper_isZero (hx : x ∉ U) :
    IsZero (U.sheafRestrict.obj ((AbelianSheafInjectives.Construction.abelianSheafSkyscraper X x).obj I)) := by
  classical
  apply IsZero.of_full_of_faithful_of_isZero
    (sheafToPresheaf (_root_.Opens.grothendieckTopology U) AddCommGrpCat.{u})
  apply Functor.isZero
  intro V
  have hV : x ∉ Subtype.val '' (V.unop : Set U) := by
    rintro ⟨y, _, heq⟩
    exact hx (heq ▸ y.property)
  change IsZero (if x ∈ Subtype.val '' (V.unop : Set U) then I else ⊤_ AddCommGrpCat.{u})
  rw [ite_eq_right hV]
  exact (isZero_zero AddCommGrpCat.{u}).of_iso (HasZeroObject.zeroIsoTerminal).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SkyscraperRestriction.Construction
