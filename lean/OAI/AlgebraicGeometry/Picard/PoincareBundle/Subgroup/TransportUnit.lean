import OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit

/-! # Transport Unit -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TransportUnit

noncomputable section

/-! The global identity diagram gives identity fiber transport on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
open Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {H A : Over S} [GrpObj H] [GrpObj A]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem transport_unit
    (hu : pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := snd H A) (f₂ := NormalizedKernelTranslation.action i) t.hom (NormalizedKernelTranslation.sectionMap (H := H) (A := A)) (𝟙 A) (𝟙 A)
      (NormalizedKernelTranslation.section_source (H := H) (A := A)) (NormalizedKernelTranslation.section_action i) = 𝟙 (Line.Fibers.fiber L (𝟙 A)))
    {T : Over S} (x : T ⟶ A) (hx : ((1 : T ⟶ H) ≫ i) * x = x) :
    TranslationFibers.transportIso i L t x x 1 hx = Iso.refl (Line.Fibers.fiber L x) := by
  let s := NormalizedKernelTranslation.sectionMap (H := H) (A := A)
  have hp : lift (1 : T ⟶ H) x = x ≫ s := by
    change lift (1 : T ⟶ H) x = x ≫ lift (1 : A ⟶ H) (𝟙 A)
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  have h₀ := congrArg (fun q : Line.Fibers.fiber L (𝟙 A) ⟶ Line.Fibers.fiber L (𝟙 A) =>
    pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
      (f₁ := 𝟙 A) (f₂ := 𝟙 A) q x x x (Category.comp_id x) (Category.comp_id x)) hu
  have hid := PullHom.pullHom_identity (F := Geometric.KernelLinearization.overModulePullbacks S) (L := L.sheaf) (x := 𝟙 A)
    x x (Category.comp_id x)
  have h₁ := pullHom_pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) (M₁ := L.sheaf) (M₂ := L.sheaf)
    (f₁ := snd H A) (f₂ := NormalizedKernelTranslation.action i) t.hom s (𝟙 A) (𝟙 A) x x x
    (NormalizedKernelTranslation.section_source (H := H) (A := A)) (NormalizedKernelTranslation.section_action i) (Category.comp_id x) (Category.comp_id x)
  have h₂ := PullHom.pullHom_congr (F := Geometric.KernelLinearization.overModulePullbacks S) (L := L.sheaf) (M := L.sheaf)
    (x := snd H A) (y := NormalizedKernelTranslation.action i) t.hom (lift (1 : T ⟶ H) x) (x ≫ s) hp x x
    (lift_snd _ _) ((TranslationFibers.action_pair i 1 x).trans hx)
    (by rw [Category.assoc, NormalizedKernelTranslation.section_source, Category.comp_id])
    (by rw [Category.assoc, NormalizedKernelTranslation.section_action, Category.comp_id])
  apply Iso.ext
  exact (TranslationFibers.transportIso_hom i L t x x 1 hx).trans (h₂.trans (h₁.symm.trans (h₀.trans hid)))

/-- Identity-normalized global translation is identity transport on every test scheme. -/
theorem normalized_transport_unit {T : Over S} (x : T ⟶ A)
    (hx : ((1 : T ⟶ H) ≫ i) * x = x) :
    TranslationFibers.transportIso i L (NormalizedTranslationUnit.translation i L t) x x 1 hx =
      Iso.refl (Line.Fibers.fiber L x) :=
  transport_unit i L (NormalizedTranslationUnit.translation i L t)
    (NormalizedTranslationUnit.unit_diagram i L t) x hx

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TransportUnit
