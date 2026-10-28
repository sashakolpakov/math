import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Flat Base -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatBase

noncomputable section

/-! An isomorphism on the direct image of the structure sheaf persists
under flat base change, using the actual pushout of sections on affine opens. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

namespace Construction.FlatBaseChangeFunctions

variable {X Y Z P : Scheme.{u}} [NoetherianSpace X]
variable (q : X ⟶ Y) (p : Z ⟶ Y) [Flat p] (r : P ⟶ X) (v : P ⟶ Z)
variable (H : IsPullback r v q p) (hq : ∀ U : Y.Opens, IsIso (q.app U))

include H hq

theorem isIso_app_on_affine (U : Y.Opens) (hU : IsAffineOpen U)
    (V : Z.Opens) (hV : IsAffineOpen V) (hVU : V ≤ p ⁻¹ᵁ U) : IsIso (v.app V) := by
  have he : v ⁻¹ᵁ V = r ⁻¹ᵁ (q ⁻¹ᵁ U) ⊓ v ⁻¹ᵁ V := by
    change v ⁻¹ᵁ V = (r ≫ q) ⁻¹ᵁ U ⊓ v ⁻¹ᵁ V
    rw [H.w]
    exact (inf_eq_right.mpr (v.preimage_mono hVU)).symm
  have ha := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hVU le_rfl he hU hV
    (NoetherianSpace.isCompact (q ⁻¹ᵁ U : Set X))
    (fun _ _ _ _ _ _ _ _ => NoetherianSpace.isCompact _)
  have hp := (isIso_pushoutSection_iff H hVU le_rfl he).mp ha
  have : IsIso (q.appLE U (q ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact hq U
  have hi := hp.isIso_inr_of_isIso
  change IsIso (v.appLE V (v ⁻¹ᵁ V) le_rfl) at hi
  rw [Scheme.Hom.appLE_eq_app] at hi
  exact hi

theorem isIso_ringSheaf : IsIso v.toRingCatSheafHom := by
  let B := Σ U : Y.affineOpens, {V : Z.affineOpens // V.1 ≤ p ⁻¹ᵁ U.1}
  let O : B → Z.Opens := fun i => i.2.1.1
  have hB : Opens.IsBasis (Set.range O) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro W z hz
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, _⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p z)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open
        (show z ∈ W ⊓ p ⁻¹ᵁ U from ⟨hz, hzU⟩) (W ⊓ p ⁻¹ᵁ U).isOpen
    exact ⟨V, ⟨⟨⟨U, hU⟩, ⟨⟨V, hV⟩, hVW.trans inf_le_right⟩⟩, rfl⟩,
      hzV, hVW.trans inf_le_left⟩
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro i
  have hi := isIso_app_on_affine q p r v H hq i.1.1 i.1.2 i.2.1.1 i.2.1.2 i.2.2
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ((ConcreteCategory.isIso_iff_bijective (v.app (O i))).mp hi)

theorem isIso_app (U : Z.Opens) : IsIso (v.app U) := by
  have hs := isIso_ringSheaf q p r v H hq
  let e := @asIso _ _ _ _ v.toRingCatSheafHom hs
  let e' := (sheafToPresheaf _ _).mapIso e
  have hi : IsIso (v.toRingCatSheafHom.hom.app (.op U)) := (e'.app (.op U)).isIso_hom
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ((ConcreteCategory.isIso_iff_bijective (v.toRingCatSheafHom.hom.app (.op U))).mp hi)

theorem isIso_unit : IsIso (SheafOfModules.unitToPushforwardObjUnit v.toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ((ConcreteCategory.isIso_iff_bijective (v.app U)).mp (isIso_app q p r v H hq U))

def iso : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ≅ (Scheme.Modules.pushforward v).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P) :=
  @asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit v.toRingCatSheafHom)
    (isIso_unit q p r v H hq)

end Construction.FlatBaseChangeFunctions

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatBase
