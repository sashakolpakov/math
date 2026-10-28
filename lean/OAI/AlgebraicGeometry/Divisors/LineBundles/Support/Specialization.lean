import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Integrality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Closure

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: specialization of a global integral closed support

The actual integral support deformation has a nonzero global parameter.
Its finite effective divisor lies on the pullback of the ambient normal
cone. Pushing this entire divisor along that closed fiber gives a finite
cycle on the ambient global cone.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Order
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- The regular parameter on the support deformation is pulled from the ambient deformation. -/
def globalSupportParameterSection : Γ(Global.SupportDeformation.BundleCycles.globalSupportDeformation I P, ⊤) :=
  (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P).appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection I)

theorem closedSupportDeformationParameterSection {R : Type u} [CommRing R] (J Q : Ideal R) :
    (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion J Q).appTop (Affine.Specialization.BundleCycles.affineDeformationParameterSection J) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (J.map (Ideal.Quotient.mk Q)) := by
  let f : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra J) ⟶
      CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (J.map (Ideal.Quotient.mk Q))) :=
    CommRingCat.ofHom (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap J Q)
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f) (Deformation.Iff.BundleCycles.deformationParameter J)
  change (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (J.map (Ideal.Quotient.mk Q))))).inv
      (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap J Q (Deformation.Iff.BundleCycles.deformationParameter J)) =
    (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion J Q).appTop (Affine.Specialization.BundleCycles.affineDeformationParameterSection J) at h
  rw [Deformation.Closure.BundleCycles.closedSupportDeformationRingMap_parameter] at h
  exact h.symm

/-- Every support chart carries exactly its original Laurent parameter section. -/
theorem globalSupportParameterSection_on_chart (U : X.AffineZariskiSite) :
    ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop (globalSupportParameterSection I P) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) := by
  have h := congrArg (fun k => k.appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection I))
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_on_chart I P U)
  change ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop (globalSupportParameterSection I P) =
    (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion (I.ideal U) (P.ideal U)).appTop
      (((Global.Deformation.BundleCycles.globalDeformationCover I).f U).appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection I)) at h
  rw [Global.Specialization.BundleCycles.globalDeformationParameterSection_on_chart I U] at h
  exact h.trans (closedSupportDeformationParameterSection (I.ideal U) (P.ideal U))

/-- The actual zero fiber of the closed support deformation inside the ambient cone. -/
def globalSupportSpecialFiber : Scheme :=
  pullback (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)

def globalSupportSpecialFiberInclusion : globalSupportSpecialFiber I P ⟶ Global.SupportDeformation.BundleCycles.globalSupportDeformation I P :=
  pullback.fst _ _

def globalSupportSpecialFiberMap : globalSupportSpecialFiber I P ⟶ Global.SpecialFiber.BundleCycles.globalSpecialFiber I :=
  pullback.snd _ _

instance globalSupportSpecialFiberInclusion_isClosedImmersion :
    IsClosedImmersion (globalSupportSpecialFiberInclusion I P) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.fst (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)))

instance globalSupportSpecialFiberMap_isClosedImmersion :
    IsClosedImmersion (globalSupportSpecialFiberMap I P) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.snd (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)))

/-- The pullback cone contains exactly the vanishing locus of the support's parameter. -/
theorem globalSupportSpecialFiberInclusion_range :
    Set.range (globalSupportSpecialFiberInclusion I P) =
      ((Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).basicOpen (globalSupportParameterSection I P) :
        Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P))ᶜ := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (IsPullback.of_hasPullback (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  change Set.range (globalSupportSpecialFiberInclusion I P) =
    Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P ⁻¹' Set.range (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) at h
  rw [Global.Specialization.BundleCycles.globalSpecialFiberMap_range I, Set.preimage_compl] at h
  have hb := Scheme.preimage_basicOpen_top (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P)
    (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
  exact h.trans (congrArg
    (fun U : (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).Opens => (U : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P))ᶜ) hb)

variable [IsIntegral P.subscheme]

theorem globalSupportParameterSection_ne_zero : globalSupportParameterSection I P ≠ 0 := by
  let x : P.subscheme := Classical.choice inferInstance
  obtain ⟨U, y, _⟩ := P.subschemeCover.openCover.exists_eq x
  have : Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) := ⟨y⟩
  have : IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) := Integrality.BundleCycles.supportCoefficientRing_isDomain P U
  intro hz
  have h := congrArg ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop hz
  rw [globalSupportParameterSection_on_chart I P U] at h
  exact Affine.Specialization.BundleCycles.affineDeformationParameterSection_ne_zero (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
    (h.trans (map_zero ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop.hom))

variable [AlgebraicGeometry.IsNoetherian X]

/-- The finite divisor of t on the global integral closed-support deformation. -/
def globalSupportParameterDivisor : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P →₀ ℤ :=
  RegularDivisor.BundleCycles.regularFunctionDivisor (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (globalSupportParameterSection I P)

theorem globalSupportParameterDivisor_support :
    ((globalSupportParameterDivisor I P).support : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) ⊆
      Set.range (globalSupportSpecialFiberInclusion I P) := by
  rw [globalSupportSpecialFiberInclusion_range]
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset _ _

def globalSupportFiberPointEmbedding : globalSupportSpecialFiber I P ↪ Global.SupportDeformation.BundleCycles.globalSupportDeformation I P :=
  ⟨globalSupportSpecialFiberInclusion I P, (globalSupportSpecialFiberInclusion I P).isClosedEmbedding.injective⟩

/-- The complete divisor of t transported onto its closed fiber. -/
def globalSupportFiberCycle : globalSupportSpecialFiber I P →₀ ℤ :=
  Finsupp.comapDomain (globalSupportFiberPointEmbedding I P) (globalSupportParameterDivisor I P)
    (globalSupportFiberPointEmbedding I P).injective.injOn

theorem globalSupportFiberCycle_push :
    Finsupp.embDomain (globalSupportFiberPointEmbedding I P) (globalSupportFiberCycle I P) =
      globalSupportParameterDivisor I P :=
  Finsupp.embDomain_comapDomain (globalSupportParameterDivisor_support I P)

def globalSupportConePointEmbedding : globalSupportSpecialFiber I P ↪ Global.SpecialFiber.BundleCycles.globalSpecialFiber I :=
  ⟨globalSupportSpecialFiberMap I P, (globalSupportSpecialFiberMap I P).isClosedEmbedding.injective⟩

/-- Specialization of an actual integral closed support as a finite cycle on the ambient cone. -/
def globalClosedSupportSpecialization : Global.SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  Finsupp.embDomain (globalSupportConePointEmbedding I P) (globalSupportFiberCycle I P)

theorem globalClosedSupportSpecialization_at_support (x : globalSupportSpecialFiber I P) :
    globalClosedSupportSpecialization I P (globalSupportSpecialFiberMap I P x) =
      globalSupportParameterDivisor I P (globalSupportSpecialFiberInclusion I P x) :=
  Finsupp.embDomain_apply_self _ _ _

theorem globalClosedSupportSpecialization_nonnegative (x : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) :
    0 ≤ globalClosedSupportSpecialization I P x := by
  classical
  by_cases hx : x ∈ Set.range (globalSupportSpecialFiberMap I P)
  · obtain ⟨y, rfl⟩ := hx
    rw [globalClosedSupportSpecialization_at_support]
    exact RegularDivisor.BundleCycles.regularFunctionDivisor_nonnegative _ _ (globalSupportParameterSection_ne_zero I P) _
  · have hz : globalClosedSupportSpecialization I P x = 0 :=
      Finsupp.embDomain_of_notMem_range _ _ _ hx
    exact hz.symm ▸ le_refl 0

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization.BundleCycles
