import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.DescentRecovery

/-! # Morphism Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.MorphismDescent

noncomputable section

/-!
# Descending compatible actual sheaf morphisms to a specified recovered line
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
  (hD : Line.Bundles.IsLine (D.obj PUnit.unit)) (P : Line.Bundles.LineBundle Y)
  (e : (Scheme.Modules.pullback f).obj P.sheaf ≅ D.obj PUnit.unit)
  (he : (Scheme.Modules.pullback (pullback.fst f f)).map e.hom ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f) pullback.condition).hom.app P.sheaf ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map e.hom)
  (M : Y.Modules) (a : (Scheme.Modules.pullback f).obj M ⟶ D.obj PUnit.unit)
  (ha : (Scheme.Modules.pullback (pullback.fst f f)).map a ≫ (Geometric.CechInvariant.relationGluing f D).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f) pullback.condition).hom.app M ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map a)

/-- The genuine compatible map first descends to the actual invariant sheaf. -/
def invariantLift : M ⟶ Geometric.CechInvariant.ordinaryInvariantSheaf f D :=
  (Cech.InvariantUniversal.existsUnique_lift f (pullback.fst f f) (pullback.snd f f) pullback.condition
    (D.obj PUnit.unit) (Geometric.CechInvariant.relationGluing f D) M ⟨a, ha⟩).choose

omit [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] in
/-- Its pullback is precisely the original compatible morphism. -/
theorem invariantLift_fac : (Scheme.Modules.pullback f).map (invariantLift f D M a ha) ≫ Geometric.CechInvariant.ordinaryComparison f D = a :=
  (Cech.InvariantUniversal.existsUnique_lift f (pullback.fst f f) (pullback.snd f f) pullback.condition
    (D.obj PUnit.unit) (Geometric.CechInvariant.relationGluing f D) M ⟨a, ha⟩).choose_spec.1

/-- Transport the actual invariant lift to the specified recovered quotient line. -/
def descendedHom : M ⟶ P.sheaf :=
  invariantLift f D M a ha ≫ (Bilinear.DescentRecovery.outputIso f D hD P e he).inv

/-- The constructed quotient morphism satisfies its exact prescribed recovery equation. -/
theorem descendedHom_fac : (Scheme.Modules.pullback f).map (descendedHom f D hD P e he M a ha) ≫ e.hom = a := by
  unfold descendedHom
  erw [Functor.map_comp]
  erw [Category.assoc, Bilinear.DescentRecovery.outputIso_inv_fac]
  exact invariantLift_fac f D M a ha

include hD he ha in
/-- The constructed morphism is the unique actual quotient map with the prescribed recovery. -/
theorem existsUnique_hom : ∃! t : M ⟶ P.sheaf, (Scheme.Modules.pullback f).map t ≫ e.hom = a := by
  refine ⟨descendedHom f D hD P e he M a ha, descendedHom_fac f D hD P e he M a ha, ?_⟩
  intro t ht
  apply (cancel_mono (Bilinear.DescentRecovery.outputIso f D hD P e he).hom).mp
  have hu := (Cech.InvariantUniversal.existsUnique_lift f (pullback.fst f f) (pullback.snd f f)
    pullback.condition (D.obj PUnit.unit) (Geometric.CechInvariant.relationGluing f D) M ⟨a, ha⟩).choose_spec.2
  have ht' : (Scheme.Modules.pullback f).map (t ≫ (Bilinear.DescentRecovery.outputIso f D hD P e he).hom) ≫
      Geometric.CechInvariant.ordinaryComparison f D = a := by
    rw [Functor.map_comp]
    erw [Category.assoc, Bilinear.DescentRecovery.outputIso_fac]
    exact ht
  have h := hu _ ht'
  change t ≫ (Bilinear.DescentRecovery.outputIso f D hD P e he).hom =
    (invariantLift f D M a ha ≫ (Bilinear.DescentRecovery.outputIso f D hD P e he).inv) ≫
      (Bilinear.DescentRecovery.outputIso f D hD P e he).hom
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h

/-- A genuine invertible map between lines remains invertible after this constructed descent. -/
theorem descendedHom_isIso (hM : Line.Bundles.IsLine M) (hiso : IsIso a) :
    IsIso (descendedHom f D hD P e he M a ha) := by
  have hcomp : IsIso ((Scheme.Modules.pullback f).map (descendedHom f D hD P e he M a ha) ≫ e.hom) := by
    erw [descendedHom_fac]
    exact hiso
  have hp : IsIso ((Scheme.Modules.pullback f).map (descendedHom f D hD P e he M a ha)) :=
    (@isIso_comp_right_iff _ _ _ _ _ _ _ e.isIso_hom).mp hcomp
  exact FaithfulPullback.isIso_of_pullback f (descendedHom f D hD P e he M a ha) hM P.isLine hp

/-- Descending an actual line-bundle isomorphism produces its actual quotient isomorphism. -/
def descendedIso (hM : Line.Bundles.IsLine M) (hiso : IsIso a) : M ≅ P.sheaf :=
  @asIso _ _ _ _ (descendedHom f D hD P e he M a ha)
    (descendedHom_isIso f D hD P e he M a ha hM hiso)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.MorphismDescent
