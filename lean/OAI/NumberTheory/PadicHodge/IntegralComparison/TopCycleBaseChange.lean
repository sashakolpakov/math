import OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Top Cycle Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopCycleBaseChange

noncomputable section

/-! The canonical top-cycle class commutes with exact additive functors.
This keeps the normalization of scalar-extension homology comparisons explicit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w w'
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w'} D]
  [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

open OAI.NumberTheory.PadicHodge.IntegralComparison.TopHomologyCokernel

theorem shortClass_map (S : ShortComplex C) (hg : S.g = 0)
    (hF : (S.map F).g = 0) :
    TopHomologyCokernel.shortClass (S.map F) hF ≫ (S.mapHomologyIso F).hom =
      F.map (TopHomologyCokernel.shortClass S hg) := by
  let h := ShortComplex.LeftHomologyData.ofHasCokernel S hg
  have hi : (h.map F).cyclesIso.hom = (S.map F).iCycles := by
    have hi' := (h.map F).cyclesIso_hom_comp_i
    change (h.map F).cyclesIso.hom ≫ F.map (𝟙 S.X₂) = _ at hi'
    erw [F.map_id, Category.comp_id] at hi'
    exact hi'
  have hπ : TopHomologyCokernel.shortClass (S.map F) hF ≫ (h.map F).homologyIso.hom =
      F.map (cokernel.π S.f) := by
    rw [TopHomologyCokernel.shortClass, Category.assoc,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hi,
      ← Category.assoc, ShortComplex.cyclesIsoX₂_inv_hom_id, Category.id_comp]
    rfl
  rw [h.mapHomologyIso_eq F, Iso.trans_hom, ← Category.assoc, hπ,
    Functor.mapIso_hom, ← F.map_comp]
  congr 1
  change cokernel.π S.f ≫ (TopHomologyCokernel.shortIso S hg).inv = TopHomologyCokernel.shortClass S hg
  apply (cancel_mono (TopHomologyCokernel.shortIso S hg).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, TopHomologyCokernel.shortClass_iso]

theorem cycleClass_map {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (n : ι)
    (hK : IsZero (K.X (c.next n)))
    (hF : IsZero (((F.mapHomologicalComplex c).obj K).X (c.next n))) :
    TopHomologyCokernel.cycleClass ((F.mapHomologicalComplex c).obj K) n hF ≫
        ((K.sc n).mapHomologyIso F).hom = F.map (TopHomologyCokernel.cycleClass K n hK) :=
  shortClass_map F (K.sc n) (hK.eq_of_tgt _ _) (hF.eq_of_tgt _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopCycleBaseChange
