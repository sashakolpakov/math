import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiberContainment
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.SectionRestriction

/-! # Functions Local Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRigidity

noncomputable section

/-! Local constancy near a constant fiber uses global functions and allows nonreduced parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X T Y : Scheme.{u}}

theorem globalFunctions_rigidity_on_affineTube (p : X ⟶ T) [UniversallyClosed p]
    (hp : ∀ V : T.Opens, IsIso (p ∣_ V).appTop)
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 _) (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U) :
    (p ⁻¹ᵁ Proper.FiberContainment.properFiberContainmentOpen p f U).ι ≫ f =
      (p ⁻¹ᵁ Proper.FiberContainment.properFiberContainmentOpen p f U).ι ≫ (p ≫ σ ≫ f) := by
  let V := Proper.FiberContainment.properFiberContainmentOpen p f U
  let s := Family.SectionRestriction.familySectionRestrict p σ hσ V
  let F := Proper.FiberContainment.properFiberContainmentFactor p f U
  let : IsAffine U.toScheme := hU
  have := hp V
  have hs : s ≫ (p ∣_ V) = 𝟙 _ := Family.SectionRestriction.familySectionRestrict_projection p σ hσ V
  have hsi : s ≫ (p ⁻¹ᵁ V).ι = V.ι ≫ σ := Family.SectionRestriction.familySectionRestrict_inclusion p σ hσ V
  have hF : F ≫ U.ι = (p ⁻¹ᵁ V).ι ≫ f := Proper.FiberContainment.properFiberContainmentFactor_comp p f U
  have H : F = (p ∣_ V) ≫ s ≫ F := FunctionsMapRigidity.affineMap_eq_of_globalFunctions_iso (p ∣_ V) s hs F
  calc
    _ = F ≫ U.ι := hF.symm
    _ = ((p ∣_ V) ≫ s ≫ F) ≫ U.ι := congrArg (fun a => a ≫ U.ι) H
    _ = (p ∣_ V) ≫ (V.ι ≫ σ) ≫ f := by
      simp only [Category.assoc]
      rw [hF, ← Category.assoc s, hsi, Category.assoc]
    _ = ((p ∣_ V) ≫ V.ι) ≫ σ ≫ f := by simp only [Category.assoc]
    _ = _ := (congrArg (fun a => a ≫ σ ≫ f) (morphismRestrict_ι p V)).trans (Category.assoc _ _ _)

theorem globalFunctions_localRigidity (p : X ⟶ T) [UniversallyClosed p]
    (hp : ∀ V : T.Opens, IsIso (p ∣_ V).appTop)
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 _) (f : X ⟶ Y)
    (s : T) (y : Y) (hy : ∀ x : X, p x = s → f x = y) :
    ∃ V : T.Opens, s ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ f = (p ⁻¹ᵁ V).ι ≫ (p ≫ σ ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine ⟨Proper.FiberContainment.properFiberContainmentOpen p f U, ?_,
    globalFunctions_rigidity_on_affineTube p hp σ hσ f U hU⟩
  apply (Proper.FiberContainment.mem_properFiberContainmentOpen_iff p f U s).mpr
  intro x hx
  exact hy x hx ▸ hyU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsLocalRigidity
