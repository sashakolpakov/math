import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.Augmentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections

/-! # Augmentation Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AugmentationInjectivity

noncomputable section

/-! The ordered Čech augmentation is injective for an open cover, by the sheaf separation property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

theorem orderedCechSectionToCycles_injective (hU : ∀ x : X, ∃ i, x ∈ U i) :
    Function.Injective (Augmentation.orderedCechSectionToCycles c M U) := by
  intro s t hst
  apply M.isSheaf.section_ext
  intro x _
  obtain ⟨i, hi⟩ := hU x
  refine ⟨U i, le_top, hi, ?_⟩
  let a : Ordered.SectionCechIndices.OrderedCechIndex ι 0 := ⟨fun _ ↦ i, Subsingleton.strictMono (α := Fin 1) _⟩
  let F := Coefficient.ModulePresheaf.coefficientModulePresheaf c M
  have he : (∏ᶜ fun k : Fin 1 ↦ U (a.val k)) = U i := by
    rw [Affine.CechIntersections.opensProduct_eq_iInf]
    simp only [a, iInf_const]
  have h0 : (Augmentation.orderedCechSectionMap c M U 0) s = (Augmentation.orderedCechSectionMap c M U 0) t :=
    congrArg Subtype.val hst
  have h1 := congrArg (CategoryTheory.Limits.Pi.π
    (fun b : Ordered.SectionCechIndices.OrderedCechIndex ι 0 ↦ Ordered.CoefficientCechTerms.coefficientCechFactor c M U 0 b.val) a) h0
  have hp := Augmentation.orderedCechSectionMap_comp_π c M U 0 a
  have htop : F.map (homOfLE (show (∏ᶜ fun k : Fin 1 ↦ U (a.val k)) ≤ ⊤ from le_top)).op s =
      F.map (homOfLE (show (∏ᶜ fun k : Fin 1 ↦ U (a.val k)) ≤ ⊤ from le_top)).op t :=
    (ConcreteCategory.congr_hom hp s).symm.trans (h1.trans (ConcreteCategory.congr_hom hp t))
  have h2 := congrArg (F.map (homOfLE he.ge).op) htop
  have hc : F.map (homOfLE (show (∏ᶜ fun k : Fin 1 ↦ U (a.val k)) ≤ ⊤ from le_top)).op ≫
      F.map (homOfLE he.ge).op = F.map (homOfLE (show U i ≤ ⊤ from le_top)).op :=
    (F.map_comp _ _).symm.trans (congrArg F.map (Subsingleton.elim _ _))
  exact (ConcreteCategory.congr_hom hc s).symm.trans (h2.trans (ConcreteCategory.congr_hom hc t))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AugmentationInjectivity
