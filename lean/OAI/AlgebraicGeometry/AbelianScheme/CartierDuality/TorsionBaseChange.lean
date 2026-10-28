import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CoprimeTorsionIs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Torsion Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion

noncomputable section

/-!
# CartierDuality: canonical base change of native torsion maps
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- Change the defining equalizer arrows by equalities. -/
def equalizerCongr {C : Type*} [Category C] [HasEqualizers C]
    {X Y : C} {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    equalizer f g ≅ equalizer f' g' := by
  cases hf
  cases hg
  exact Iso.refl _

theorem equalizerCongr_inclusion {C : Type*} [Category C] [HasEqualizers C]
    {X Y : C} {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    (equalizerCongr hf hg).hom ≫ equalizer.ι f' g' = equalizer.ι f g := by
  cases hf
  cases hg
  exact Category.id_comp _

/-- The preserved-equalizer comparison and an arrow congruence retain
the universal inclusion, in arbitrary categories. -/
theorem preservedEqualizerCongr_inclusion
    {C D : Type*} [Category C] [Category D] [HasEqualizers C] [HasEqualizers D]
    (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
    [PreservesLimit (parallelPair f g) F]
    {f' g' : F.obj X ⟶ F.obj Y} (hf : F.map f = f') (hg : F.map g = g') :
    (PreservesEqualizer.iso F f g ≪≫ equalizerCongr hf hg).hom ≫ equalizer.ι f' g' =
      F.map (equalizer.ι f g) := by
  rw [Iso.trans_hom, Category.assoc, equalizerCongr_inclusion, PreservesEqualizer.iso_hom]
  exact equalizerComparison_comp_π _ _ _

variable {S T : Scheme.{u}} (a : T ⟶ S) (A : Over S) [GrpObj A] (n : ℕ)

/-- The power map is preserved by the monoidal base-change functor. -/
theorem power_baseChange :
    (Over.pullback a).map ((𝟙 A) ^ n) = (𝟙 ((Over.pullback a).obj A)) ^ n :=
  (((Over.pullback a).homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n).trans
    (congrArg (fun k => k ^ n) ((Over.pullback a).map_id A))

/-- The actual native torsion equalizer commutes canonically with
arbitrary scheme base change, for every integer n. -/
def torsionBaseChangeIso :
    (Over.pullback a).obj (TorsionQuotient.SubgroupFunctor.torsionScheme A n) ≅
      TorsionQuotient.SubgroupFunctor.torsionScheme ((Over.pullback a).obj A) n :=
  PreservesEqualizer.iso (Over.pullback a) ((𝟙 A) ^ n) (1 : A ⟶ A) ≪≫
    equalizerCongr (power_baseChange a A n) (Over.pullback a).map_one

/-- The canonical comparison retains the torsion inclusion. -/
theorem torsionBaseChangeIso_inclusion :
    (torsionBaseChangeIso a A n).hom ≫ TorsionQuotient.SubgroupFunctor.torsionι ((Over.pullback a).obj A) n =
      (Over.pullback a).map (TorsionQuotient.SubgroupFunctor.torsionι A n) := by
  exact preservedEqualizerCongr_inclusion (Over.pullback a) ((𝟙 A) ^ n) (1 : A ⟶ A)
    (power_baseChange a A n) (Over.pullback a).map_one

variable {A} {B : Over S} [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f]

/-- Formation of the actual induced torsion map is compatible with the
canonical native base-change comparisons. -/
theorem torsionBaseChangeIso_natural :
    (Over.pullback a).map (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) ≫ (torsionBaseChangeIso a B n).hom =
      (torsionBaseChangeIso a A n).hom ≫ CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ((Over.pullback a).map f) n := by
  let F := Over.pullback a
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι (F.obj B) n) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 (F.obj B)) ^ n) (1 : F.obj B ⟶ F.obj B)))
  apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι (F.obj B) n)).mp
  rw [Category.assoc, torsionBaseChangeIso_inclusion, ← F.map_comp, CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion,
    F.map_comp, Category.assoc, CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion, ← Category.assoc, torsionBaseChangeIso_inclusion]

/-- Isomorphisms of torsion maps on a base change transfer to the
literal base change of the original native torsion map. -/
theorem torsionMap_baseChange_isIso
    [IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ((Over.pullback a).map f) n)] :
    IsIso ((Over.pullback a).map (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n)).left := by
  let i := torsionBaseChangeIso a A n
  let j := torsionBaseChangeIso a B n
  let g := CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ((Over.pullback a).map f) n
  have he : (Over.pullback a).map (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n) = i.hom ≫ g ≫ j.inv := by
    apply (cancel_mono j.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      torsionBaseChangeIso_natural a n f
  have : IsIso ((Over.pullback a).map (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n)) := by rw [he]; infer_instance
  exact (Over.forget T).map_isIso ((Over.pullback a).map (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionBaseChange.Construction.CoprimeTorsion
