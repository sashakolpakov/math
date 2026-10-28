import OAI.AlgebraicGeometry.PELModuli.CMPoints.PointField
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Descent
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Component Field Lift -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentFieldLift

noncomputable section

/-! A descended field-valued point lifts to the same open component
as its complex realization. This retains the selected component when
using CMAbelianVariety's field-of-definition conclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem spectrum_field_extension_surjective {k l : Type} [Field k] [Field l]
    (σ : k →+* l) : Function.Surjective (Spec.map (CommRingCat.ofHom σ)) := by
  intro x
  exact ⟨IsLocalRing.closedPoint l, Subsingleton.elim _ x⟩

theorem descended_fieldPoint_range_subset {X Y : Scheme.{0}}
    (i : X ⟶ Y) {k l : Type} [Field k] [Field l] (σ : k →+* l)
    (p : Spec (.of k) ⟶ Y) (z : Spec (.of l) ⟶ X)
    (hz : z ≫ i = Spec.map (CommRingCat.ofHom σ) ≫ p) :
    Set.range p ⊆ Set.range i := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨w, hw⟩ := spectrum_field_extension_surjective σ x
  refine ⟨z w, ?_⟩
  exact (Scheme.Hom.comp_apply z i w).symm.trans
    ((congrArg (fun f : Spec (.of l) ⟶ Y => f w) hz).trans
      ((Scheme.Hom.comp_apply _ p w).trans (congrArg p hw)))

theorem exists_descended_component_point {X Y : Scheme.{0}}
    (i : X ⟶ Y) [IsOpenImmersion i]
    {k l : Type} [Field k] [Field l] (σ : k →+* l)
    (p : Spec (.of k) ⟶ Y) (z : Spec (.of l) ⟶ X)
    (hz : z ≫ i = Spec.map (CommRingCat.ofHom σ) ≫ p) :
    ∃ pX : Spec (.of k) ⟶ X,
      pX ≫ i = p ∧ Spec.map (CommRingCat.ofHom σ) ≫ pX = z := by
  let hr := descended_fieldPoint_range_subset i σ p z hz
  let pX := IsOpenImmersion.lift i p hr
  refine ⟨pX, IsOpenImmersion.lift_fac i p hr, ?_⟩
  apply (cancel_mono i).mp
  rw [Category.assoc, IsOpenImmersion.lift_fac]
  exact hz.symm

theorem CM_point_descends_on_open_component (hCMAbelianVariety : Descent.ModuliInput)
    (M : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.StandardAbelianModuli) {X : Scheme.{0}} (i : X ⟶ M.space) [IsOpenImmersion i]
    (z : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hCM : (M.abelianAt (z ≫ i)).HasCMH1) :
    ∃ F : Subfield ℂ, NumberField F ∧ ∃ p : Spec (.of F) ⟶ X,
      Spec.map (CommRingCat.ofHom F.subtype) ≫ p = z := by
  obtain ⟨F, hF, p, hp⟩ := hCMAbelianVariety M (z ≫ i) hCM
  let : NumberField F := hF
  obtain ⟨pX, _, hX⟩ := exists_descended_component_point i F.subtype p z hp.symm
  exact ⟨F, hF, pX, hX⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComponentFieldLift
