import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperBirational
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Generic Lift -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GenericLift.Construction.GenericLiftRestriction

noncomputable section

/-! Restricting a dense lift of the generic point to any nonempty open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem dominant_lift {X Y Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i]
    (g : Y ⟶ Z) [IsDominant g] (h : Set.range g ⊆ Set.range i) :
    IsDominant (IsOpenImmersion.lift i g h) := by
  constructor
  apply i.isOpenEmbedding.isEmbedding.isInducing.dense_iff.mpr
  intro x
  rw [← Set.range_comp]
  have he : i ∘ IsOpenImmersion.lift i g h = g :=
    funext (fun y => congrArg (fun a : Y ⟶ Z => a y) (IsOpenImmersion.lift_fac i g h))
  rw [he]
  exact g.denseRange (i x)

variable {X Y : Scheme.{u}} [IsIntegral Y]
variable (f : X ⟶ Y) (g : Spec Y.functionField ⟶ X)
variable (hg : g ≫ f = Y.fromSpecStalk (genericPoint Y))

theorem generic_mem (U : Y.Opens) [Nonempty U] : genericPoint Y ∈ U :=
  ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

include hg

theorem range_subset (U : Y.Opens) [Nonempty U] :
    Set.range g ⊆ Set.range (f ⁻¹ᵁ U).ι := by
  rintro _ ⟨z, rfl⟩
  refine ⟨⟨g z, ?_⟩, rfl⟩
  change f (g z) ∈ U
  rw [← Scheme.Hom.comp_apply, hg]
  have hz : z = IsLocalRing.closedPoint Y.functionField :=
    Subsingleton.elim (α := PrimeSpectrum Y.functionField) _ _
  rw [hz, Scheme.fromSpecStalk_closedPoint]
  exact generic_mem U

def lift (U : Y.Opens) [Nonempty U] : Spec Y.functionField ⟶ (f ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ U).ι g (range_subset f g hg U)

theorem lift_comp_ι (U : Y.Opens) [Nonempty U] : GenericLiftRestriction.lift f g hg U ≫ (f ⁻¹ᵁ U).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

theorem isDominant_lift [IsDominant g] (U : Y.Opens) [Nonempty U] :
    IsDominant (GenericLiftRestriction.lift f g hg U) := dominant_lift _ _ _

theorem lift_comp_restrict (U : Y.Opens) [Nonempty U] :
    GenericLiftRestriction.lift f g hg U ≫ f ∣_ U = U.fromSpecStalkOfMem (genericPoint Y) (generic_mem U) := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, lift_comp_ι, hg]
  simp

theorem lift_comp_affine (U : Y.Opens) [Nonempty U] :
    GenericLiftRestriction.lift f g hg U ≫ f ∣_ U ≫ U.toSpecΓ = Spec.map (Y.germToFunctionField U) := by
  rw [← Category.assoc, lift_comp_restrict, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GenericLift.Construction.GenericLiftRestriction
