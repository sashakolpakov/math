import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport
import OAI.AlgebraicTopology.Cohomology.Singular.SurjectiveQuasiIso

/-! # Relative Open Kernel -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenKernel

noncomputable section

/-!
# Exact sequences and naturality for relative cochains on open pairs

The actual relative complex on `U`, relative to the part lying in an ambient
open set `O`, is identified with the kernel of restriction to `U ⊓ O` by
`RelativeOpenSupport`. Here that proved identification is packaged into
genuine short exact sequences and shown natural under restriction in `U`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) {R : Type} [Ring R] (M : ModuleCat.{0} R)
variable (O : Opens X)

/-- An actual relative cochain vanishes upon restriction to the intersection open. -/
@[reassoc (attr := simp)]
theorem relativeOpenCochainInclusion_restriction (U : Opens X) :
    RelativeSequence.relativeCochainInclusion M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) ≫
      RelativeOpenSupport.openSupportCochainRestriction X M O U = 0 := by
  rw [← RelativeOpenSupport.relativeOpenIntersectionCochainsIso_restriction, ← Category.assoc,
    RelativeSequence.relativeCochainInclusion_restriction, zero_comp]

/-- The native relative cochain sequence uses the literal intersection open. -/
def relativeOpenCochainSequence (U : Opens X) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk
    (RelativeSequence.relativeCochainInclusion M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U))
    (RelativeOpenSupport.openSupportCochainRestriction X M O U)
    (relativeOpenCochainInclusion_restriction X M O U)

/-- The already proved flattening homeomorphism identifies the ordinary
relative sequence with the native intersection-open sequence. -/
def relativeOpenCochainSequenceIso (U : Opens X) :
    RelativeSequence.relativeCochainSequence M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) ≅
      relativeOpenCochainSequence X M O U :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (RelativeOpenSupport.relativeOpenIntersectionCochainsIso X M O U)
    (by simp [relativeOpenCochainSequence, RelativeSequence.relativeCochainSequence])
    (by simpa only [relativeOpenCochainSequence, RelativeSequence.relativeCochainSequence,
      Iso.refl_hom, Category.id_comp] using
      (RelativeOpenSupport.relativeOpenIntersectionCochainsIso_restriction X M O U).symm)

/-- The native open-pair sequence is genuinely short exact. -/
theorem relativeOpenCochainSequence_shortExact (U : Opens X) :
    (relativeOpenCochainSequence X M O U).ShortExact :=
  ShortComplex.shortExact_of_iso (relativeOpenCochainSequenceIso X M O U)
    (RelativeSequence.relativeCochainSequence_shortExact M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U))

/-- The native sequence is short exact in each cochain degree. -/
theorem relativeOpenCochainSequence_degreewiseShortExact (U : Opens X) (n : ℕ) :
    ((relativeOpenCochainSequence X M O U).map
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (relativeOpenCochainSequence_shortExact X M O U) n

instance openSupportCochainRestriction_epi (U : Opens X) :
    Epi (RelativeOpenSupport.openSupportCochainRestriction X M O U) :=
  (relativeOpenCochainSequence_shortExact X M O U).epi_g

instance openSupportCochainRestriction_f_epi (U : Opens X) (n : ℕ) :
    Epi ((RelativeOpenSupport.openSupportCochainRestriction X M O U).f n) := by
  infer_instance

/-- Every cochain on the actual intersection open extends degreewise to `U`. -/
theorem openSupportCochainRestriction_f_surjective (U : Opens X) (n : ℕ) :
    Function.Surjective ((RelativeOpenSupport.openSupportCochainRestriction X M O U).f n) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The native open-pair sequence is canonically the genuine kernel sequence. -/
def relativeOpenCochainSequenceIsoKernel (U : Opens X) :
    relativeOpenCochainSequence X M O U ≅
      SurjectiveQuasiIso.cochainKernelSequence (RelativeOpenSupport.openSupportCochainRestriction X M O U) :=
  ShortComplex.isoMk (RelativeOpenSupport.relativeOpenSupportKernelIso X M O U) (Iso.refl _) (Iso.refl _)
    (by simpa only [relativeOpenCochainSequence, SurjectiveQuasiIso.cochainKernelSequence,
      Iso.refl_hom, Category.comp_id] using
      RelativeOpenSupport.relativeOpenSupportKernelIso_inclusion X M O U)
    (by simp [relativeOpenCochainSequence, SurjectiveQuasiIso.cochainKernelSequence])

/-- The actual kernel sequence of restriction to `U ⊓ O` is short exact. -/
theorem openSupportKernelSequence_shortExact (U : Opens X) :
    (SurjectiveQuasiIso.cochainKernelSequence (RelativeOpenSupport.openSupportCochainRestriction X M O U)).ShortExact :=
  ShortComplex.shortExact_of_iso (relativeOpenCochainSequenceIsoKernel X M O U)
    (relativeOpenCochainSequence_shortExact X M O U)

/-- The image of relative cochains is the literal kernel of the restriction
to the actual intersection open, in every degree. -/
theorem relativeOpenCochainInclusion_range (U : Opens X) (n : ℕ) :
    LinearMap.range
        ((RelativeSequence.relativeCochainInclusion M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U)).f n).hom =
      LinearMap.ker ((RelativeOpenSupport.openSupportCochainRestriction X M O U).f n).hom :=
  (relativeOpenCochainSequence_degreewiseShortExact X M O U n).exact.moduleCat_range_eq_ker

/-- Restriction to the open complement commutes with restriction of the
ambient neighborhood. Both sides are the actual singular pullbacks. -/
@[reassoc]
theorem openSupportCochainRestriction_naturality {U V : Opens X} (i : U ⟶ V) :
    RelativeOpenSupport.openSupportCochainRestriction X M O V ≫
        Functor.singularPullback M ((Opens.toTopCat X).map
          (homOfLE (inf_le_inf_right O i.le))) =
      Functor.singularPullback M ((Opens.toTopCat X).map i) ≫
        RelativeOpenSupport.openSupportCochainRestriction X M O U := by
  rw [← Functor.singularPullback_comp, ← Functor.singularPullback_comp]
  rfl

/-- The actual restriction map between kernels for nested open neighborhoods. -/
def openSupportKernelRestriction {U V : Opens X} (i : U ⟶ V) :
    kernel (RelativeOpenSupport.openSupportCochainRestriction X M O V) ⟶
      kernel (RelativeOpenSupport.openSupportCochainRestriction X M O U) :=
  kernel.map (RelativeOpenSupport.openSupportCochainRestriction X M O V) (RelativeOpenSupport.openSupportCochainRestriction X M O U)
    (Functor.singularPullback M ((Opens.toTopCat X).map i))
    (Functor.singularPullback M ((Opens.toTopCat X).map (homOfLE (inf_le_inf_right O i.le))))
    (openSupportCochainRestriction_naturality X M O i)

@[reassoc (attr := simp)]
theorem openSupportKernelRestriction_inclusion {U V : Opens X} (i : U ⟶ V) :
    openSupportKernelRestriction X M O i ≫ kernel.ι (RelativeOpenSupport.openSupportCochainRestriction X M O U) =
      kernel.ι (RelativeOpenSupport.openSupportCochainRestriction X M O V) ≫
        Functor.singularPullback M ((Opens.toTopCat X).map i) :=
  kernel.lift_ι _ _ _

/-- The genuine relative-to-kernel identification is natural on open neighborhoods. -/
@[reassoc]
theorem relativeOpenSupportKernelIso_naturality {U V : Opens X} (i : U ⟶ V) :
    (RelativeOpenSupport.relativeCochainPresheaf M X (O : Set X)).map i.op ≫
        (RelativeOpenSupport.relativeOpenSupportKernelIso X M O U).hom =
      (RelativeOpenSupport.relativeOpenSupportKernelIso X M O V).hom ≫ openSupportKernelRestriction X M O i := by
  apply (cancel_mono (kernel.ι (RelativeOpenSupport.openSupportCochainRestriction X M O U))).1
  calc
    _ = (RelativeOpenSupport.relativeCochainPresheaf M X (O : Set X)).map i.op ≫
        RelativeSequence.relativeCochainInclusion M (TopCat.of U) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) := by
      rw [Category.assoc, RelativeOpenSupport.relativeOpenSupportKernelIso_inclusion]
    _ = RelativeSequence.relativeCochainInclusion M (TopCat.of V) (RelativeOpenSupport.relativeOpenSubspace (O : Set X) V) ≫
        Functor.singularPullback M ((Opens.toTopCat X).map i) :=
      (RelativeOpenSupport.relativeCochainPresheafInclusion M X (O : Set X)).naturality i.op
    _ = _ := by
      rw [Category.assoc, openSupportKernelRestriction_inclusion, ← Category.assoc,
        RelativeOpenSupport.relativeOpenSupportKernelIso_inclusion]

/-- Restriction of neighborhoods gives a morphism of the native relative
short exact cochain sequences. -/
def relativeOpenCochainSequenceRestriction {U V : Opens X} (i : U ⟶ V) :
    relativeOpenCochainSequence X M O V ⟶ relativeOpenCochainSequence X M O U where
  τ₁ := (RelativeOpenSupport.relativeCochainPresheaf M X (O : Set X)).map i.op
  τ₂ := Functor.singularPullback M ((Opens.toTopCat X).map i)
  τ₃ := Functor.singularPullback M ((Opens.toTopCat X).map (homOfLE (inf_le_inf_right O i.le)))
  comm₁₂ := (RelativeOpenSupport.relativeCochainPresheafInclusion M X (O : Set X)).naturality i.op
  comm₂₃ := (openSupportCochainRestriction_naturality X M O i).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenKernel
