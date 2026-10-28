import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization

/-! # Rigidified Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Equal relative Picard values have unique normalized comparisons
on arbitrary test schemes when the group family has universal global functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A]
  (D : Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions A)

include hΓ in
set_option backward.isDefEq.respectTransparency false in
theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universal_existsUnique_normalized {T : Over S} (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) :
    ∃! e : (D.line a).sheaf ≅ (D.line b).sheaf, D.Normalized a b e := by
  let σ := (lift (𝟙 T) (1 : T ⟶ A)).left
  have hσ : σ ≫ (fst T A).left = 𝟙 T.left := congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A))
  have hLM : Nonempty ((D.line a).sheaf ≅ (D.line b).sheaf) :=
    Universal.BundleNormalization.Construction.universal_bundleIso_of_relativePicard_eq A T hΓ (D.line a) (D.line b) σ hσ
      (D.frame a ≪≫ (D.frame b).symm) h
  have hF := hΓ.of_isPullback (pullback.snd T.hom A.hom) (pullback.fst T.hom A.hom) T.hom
    (IsPullback.of_hasPullback T.hom A.hom).flip
  obtain ⟨e, he, hu⟩ := Universal.BundleNormalization.Construction.universal_existsUnique_bundleIso_with_section_fiber (fst T A).left σ hσ hF
    (D.line a) (D.line b) hLM (D.frame a ≪≫ (D.frame b).symm)
  have hn (d : (D.line a).sheaf ≅ (D.line b).sheaf) : D.Normalized a b d ↔
      (Scheme.Modules.pullback σ).map d.hom = (D.frame a ≪≫ (D.frame b).symm).hom := by
    constructor
    · intro hd
      dsimp only [Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.Normalized] at hd
      exact (cancel_mono (D.frame b).hom).mp (by
        simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hd)
    · intro hd
      change (Scheme.Modules.pullback σ).map d.hom ≫ (D.frame b).hom = (D.frame a).hom
      rw [hd]
      simp
  exact ⟨e, (hn e).mpr he, fun d hd => hu d ((hn d).mp hd)⟩

def Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalComparison {T : Over S} (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) : (D.line a).sheaf ≅ (D.line b).sheaf :=
  Classical.choose (D.universal_existsUnique_normalized hΓ a b h)

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalComparison_normalized {T : Over S} (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) : D.Normalized a b (D.universalComparison hΓ a b h) :=
  (Classical.choose_spec (D.universal_existsUnique_normalized hΓ a b h)).1

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalComparison_unique {T : Over S} (a b : T ⟶ B)
    (h : D.relativeValue a = D.relativeValue b) (e : (D.line a).sheaf ≅ (D.line b).sheaf)
    (he : D.Normalized a b e) : e = D.universalComparison hΓ a b h :=
  (Classical.choose_spec (D.universal_existsUnique_normalized hΓ a b h)).2 e he

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalComparison_self {T : Over S} (a : T ⟶ B) :
    D.universalComparison hΓ a a rfl = Iso.refl _ := by
  symm
  apply D.universalComparison_unique hΓ
  simp [Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.Normalized]

theorem Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine.universalComparison_comp {T : Over S} (a b c : T ⟶ B)
    (hab : D.relativeValue a = D.relativeValue b) (hbc : D.relativeValue b = D.relativeValue c) :
    D.universalComparison hΓ a b hab ≪≫ D.universalComparison hΓ b c hbc = D.universalComparison hΓ a c (hab.trans hbc) := by
  apply D.universalComparison_unique hΓ
  change (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).map
    ((D.universalComparison hΓ a b hab).hom ≫ (D.universalComparison hΓ b c hbc).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, D.universalComparison_normalized hΓ b c hbc, D.universalComparison_normalized hΓ a b hab]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
