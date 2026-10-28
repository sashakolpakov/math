import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.GlobalDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.LineDescentUniqueness

/-! # Descent Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.DescentRecovery

noncomputable section

/-!
# Descend an equivariant bilinear map to the specified recovered quotient line
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Line.Bundles.IsLine (D.obj PUnit.unit)) (M N P : Line.Bundles.LineBundle Y)
  {A B : X.Modules} (eM : (Scheme.Modules.pullback f).obj M.sheaf ≅ A)
  (eN : (Scheme.Modules.pullback f).obj N.sheaf ≅ B)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B (D.obj PUnit.unit))
  (hβ : GlobalDescent.Compatible f D M N eM eN β)
  (eP : (Scheme.Modules.pullback f).obj P.sheaf ≅ D.obj PUnit.unit)
  (hP : (Scheme.Modules.pullback (pullback.fst f f)).map eP.hom ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app P.sheaf ≫ (Scheme.Modules.pullback (pullback.snd f f)).map eP.hom)

/-- The specified quotient recovery is canonically isomorphic to the effective invariant line. -/
def outputIso : P.sheaf ≅ (Ordinary.GlobalLineDescent.descendedLine f D hD).sheaf :=
  (Ordinary.LineDescentUniqueness.existsUnique_iso f D hD P eP hP).choose

/-- The output identification recovers the specified actual pullback isomorphism. -/
theorem outputIso_fac : (Scheme.Modules.pullback f).map (outputIso f D hD P eP hP).hom ≫
    Geometric.CechInvariant.ordinaryComparison f D = eP.hom :=
  (Ordinary.LineDescentUniqueness.existsUnique_iso f D hD P eP hP).choose_spec.1

/-- The inverse output identification has the corresponding canonical recovery equation. -/
theorem outputIso_inv_fac : (Scheme.Modules.pullback f).map (outputIso f D hD P eP hP).inv ≫ eP.hom =
    Geometric.CechInvariant.ordinaryComparison f D := by
  rw [← outputIso_fac f D hD P eP hP]
  erw [← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, (Scheme.Modules.pullback f).map_id, Category.id_comp]

/-- The equivariant actual product descends to the specified output line bundle. -/
def descendedBilinear : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf P.sheaf :=
  (GlobalDescent.descendedBilinear f D hD M N eM eN β hβ).postcomp
    (outputIso f D hD P eP hP).inv

/-- The descended bilinear map has its explicit represented quotient sheaf morphism. -/
theorem toHom_descendedBilinear : BilinearPullback.toHom (descendedBilinear f D hD M N P eM eN β hβ eP hP) =
    GlobalDescent.descendedHom f D hD M N eM eN β hβ ≫ (outputIso f D hD P eP hP).inv := by
  unfold descendedBilinear
  rw [BilinearPullback.toHom_postcomp, GlobalDescent.toHom_descendedBilinear]

/-- The new quotient product recovers exactly the original bilinear operation through all three specified fiber identifications. -/
theorem descendedBilinear_fac :
    (Scheme.Modules.pullback f).map (BilinearPullback.toHom (descendedBilinear f D hD M N P eM eN β hβ eP hP)) ≫ eP.hom =
      GlobalDescent.coverMap f D M N eM eN β := by
  rw [toHom_descendedBilinear, Functor.map_comp]
  erw [Category.assoc, outputIso_inv_fac,
    GlobalDescent.descendedHom_fac]

include hD hβ hP in
/-- The recovered bilinear quotient map is unique, so its algebraic laws can be checked on the cover. -/
theorem existsUnique_bilinear : ∃! δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M.sheaf N.sheaf P.sheaf,
    (Scheme.Modules.pullback f).map (BilinearPullback.toHom δ) ≫ eP.hom = GlobalDescent.coverMap f D M N eM eN β := by
  refine ⟨descendedBilinear f D hD M N P eM eN β hβ eP hP,
    descendedBilinear_fac f D hD M N P eM eN β hβ eP hP, ?_⟩
  intro δ hδ
  have hd : BilinearPullback.toHom δ ≫ (outputIso f D hD P eP hP).hom =
      GlobalDescent.descendedHom f D hD M N eM eN β hβ :=
    (GlobalDescent.existsUnique_map f D hD M N eM eN β hβ).choose_spec.2 _ (by
      change (Scheme.Modules.pullback f).map (BilinearPullback.toHom δ ≫ (outputIso f D hD P eP hP).hom) ≫
        Geometric.CechInvariant.ordinaryComparison f D = GlobalDescent.coverMap f D M N eM eN β
      erw [Functor.map_comp, Category.assoc, outputIso_fac]
      exact hδ)
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change BilinearPullback.toHom δ = BilinearPullback.toHom _
  rw [toHom_descendedBilinear]
  apply (cancel_mono (outputIso f D hD P eP hP).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hd

/-- Invertibility of the genuine source product implies invertibility of the recovered quotient product. -/
theorem descendedBilinear_isIso (hiso : IsIso (BilinearPullback.toHom β)) :
    IsIso (BilinearPullback.toHom (descendedBilinear f D hD M N P eM eN β hβ eP hP)) := by
  rw [toHom_descendedBilinear]
  have : IsIso (GlobalDescent.descendedHom f D hD M N eM eN β hβ) :=
    GlobalDescent.descendedHom_isIso f D hD M N eM eN β hβ hiso
  infer_instance

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.DescentRecovery
