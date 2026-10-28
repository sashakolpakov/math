import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupFunctor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection

/-! # Block Groups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockGroups.Construction

noncomputable section

/-!
Torsion block schemes are constructed as fixed subgroups of the actual
torsion endomorphisms. For etale torsion they are finite etale. Projector
lifts on the abelian scheme need not themselves be globally idempotent.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {T : Over S} [GrpObj T] [IsCommMonObj T]

local instance difference_isMonHom (p : T ⟶ T) [IsMonHom p] : IsMonHom (p / 𝟙 T) := by
  apply GroupMaps.Construction.isMonHom_of_pointwise
  · intro X
    rw [GrpObj.comp_div, MonObj.one_comp, Category.comp_id, div_self']
  · intro X x y
    simp only [GrpObj.comp_div, MonObj.mul_comp, Category.comp_id, mul_div_mul_comm]

def fixedPointScheme (p : T ⟶ T) [IsMonHom p] : Over S :=
  Picard.PoincareBundle.Kernel.Scheme.kernelObject (p / 𝟙 T)

instance fixedPointScheme_group (p : T ⟶ T) [IsMonHom p] : GrpObj (fixedPointScheme p) :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup (p / 𝟙 T)

instance fixedPointScheme_commutative (p : T ⟶ T) [IsMonHom p] :
    IsCommMonObj (fixedPointScheme p) :=
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative (p / 𝟙 T)

def fixedPointInclusion (p : T ⟶ T) [IsMonHom p] : fixedPointScheme p ⟶ T :=
  Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p / 𝟙 T)

instance fixedPointInclusion_mono (p : T ⟶ T) [IsMonHom p] : Mono (fixedPointInclusion p) :=
  inferInstanceAs (Mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p / 𝟙 T)))

instance fixedPointInclusion_isMonHom (p : T ⟶ T) [IsMonHom p] :
    IsMonHom (fixedPointInclusion p) := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_isMonHom (p / 𝟙 T)

theorem fixedPointInclusion_fixed (p : T ⟶ T) [IsMonHom p] :
    fixedPointInclusion p ≫ p = fixedPointInclusion p := by
  change Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p / 𝟙 T) ≫ p = _
  have h := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp (p / 𝟙 T)
  rw [GrpObj.comp_div, Category.comp_id, div_eq_one] at h
  exact h

def fixedPointLift (p : T ⟶ T) [IsMonHom p] {X : Over S}
    (x : X ⟶ T) (hx : x ≫ p = x) : X ⟶ fixedPointScheme p :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (p / 𝟙 T) X).symm
    ⟨x, by
      change x ≫ (p / 𝟙 T) = 1
      rw [GrpObj.comp_div, Category.comp_id, hx, div_self']⟩

@[simp]
theorem fixedPointLift_inclusion (p : T ⟶ T) [IsMonHom p] {X : Over S}
    (x : X ⟶ T) (hx : x ≫ p = x) : fixedPointLift p x hx ≫ fixedPointInclusion p = x :=
  pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
def fixedPointEqualizerIso (p : T ⟶ T) [IsMonHom p] :
    equalizer p (𝟙 T) ≅ fixedPointScheme p := by
  have hj : equalizer.ι p (𝟙 T) ≫ p = equalizer.ι p (𝟙 T) := by
    simpa only [Category.comp_id] using equalizer.condition p (𝟙 T)
  let d := fixedPointLift p (equalizer.ι p (𝟙 T)) hj
  let c := equalizer.lift (fixedPointInclusion p)
    ((fixedPointInclusion_fixed p).trans (Category.comp_id _).symm)
  refine ⟨d, c, ?_, ?_⟩
  · apply equalizer.hom_ext
    simp only [Category.assoc, c, equalizer.lift_ι, d,
      fixedPointLift_inclusion, Category.id_comp]
  · apply (cancel_mono (fixedPointInclusion p)).mp
    simp only [Category.assoc, d, fixedPointLift_inclusion, c,
      equalizer.lift_ι, Category.id_comp]

/-- Fixed subgroup schemes of finite etale groups are finite etale. -/
theorem fixedPointScheme_finite_etale [IsFinite T.hom] [Etale T.hom]
    (p : T ⟶ T) [IsMonHom p] :
    IsFinite (fixedPointScheme p).hom ∧ Etale (fixedPointScheme p).hom := by
  have : IsOpenImmersion (equalizer.ι p (𝟙 T)).left := EtaleDetection.Construction.equalizer_openImmersion p (𝟙 T)
  have : IsFinite (equalizer.ι p (𝟙 T)).left := inferInstance
  have : IsFinite (equalizer p (𝟙 T)).hom := by
    rw [← (equalizer.ι p (𝟙 T)).w]
    infer_instance
  have : Etale (equalizer p (𝟙 T)).hom := by
    rw [← (equalizer.ι p (𝟙 T)).w]
    infer_instance
  have : IsIso (fixedPointEqualizerIso p).inv.left :=
    (Over.forget S).map_isIso (fixedPointEqualizerIso p).inv
  rw [← (fixedPointEqualizerIso p).inv.w]
  exact ⟨inferInstance, inferInstance⟩

variable {P : Over S}

/-- A supported family factors through the constructed block group with
its original finite locally free model. -/
def supportedBlockSubgroup_model
    (p : T ⟶ T) [IsMonHom p] (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup T P) (R : F.Model)
    (hsupport : SubgroupFunctor.Construction.SupportedOn F p) :
    (SubgroupTransport.Construction.relativeSubgroupPullback (fixedPointInclusion p) F).Model :=
  SubgroupTransport.Construction.relativeSubgroupPullback_model (fixedPointInclusion p) F R
    (fixedPointLift p R.toGroup ((SubgroupFunctor.Construction.supportedOn_iff_model_equation F R p).mp hsupport))
    (fixedPointLift_inclusion _ _ _)

theorem supportedBlockSubgroup_image
    (p : T ⟶ T) [IsMonHom p] (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup T P)
    (hsupport : SubgroupFunctor.Construction.SupportedOn F p) :
    SubgroupTransport.Construction.relativeSubgroupImage (fixedPointInclusion p)
      (SubgroupTransport.Construction.relativeSubgroupPullback (fixedPointInclusion p) F) = F := by
  apply SubgroupTransport.Construction.relativeSubgroupPullback_image
  intro X t x hx
  exact ⟨fixedPointLift p x (hsupport X t x hx), fixedPointLift_inclusion _ _ _⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockGroups.Construction
