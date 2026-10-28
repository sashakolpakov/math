import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CharacterRanks
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalIntegralAction

/-! # Conormal Bilinear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear

noncomputable section

section

/-! The actual polarization identifies native H1 with the dual of
the constructed identity conormal. Original H1 pullback is adjoint to
the conjugate original conormal action under this pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

local instance polarizedPairingIntegral : IsIntegral A.abelian.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A.abelian
local instance polarizedPairingH1Module : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.abelian.scheme

def polarizedH1ConormalEquiv :
    SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1 ≃ₗ[ℂ]
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ] ℂ) :=
  (TangentEquiv.polarizedStructureH1TangentEquiv A).symm.trans (Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.abelian.scheme)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) (hρ : ActionData.RosatiConjugation A ρ)

include hρ

theorem polarizedStructureH1TangentEquiv_symm_pullback (a : NumberField.RingOfIntegers E)
    (x : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :
    (TangentEquiv.polarizedStructureH1TangentEquiv A).symm (StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a) x) =
      Intrinsic.Lie.nativeLieDifferential A.abelian ρ (NumberField.IsCMField.ringOfIntegersComplexConj E a)
        ((TangentEquiv.polarizedStructureH1TangentEquiv A).symm x) := by
  apply (TangentEquiv.polarizedStructureH1TangentEquiv A).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := TangentAction.polarizedStructureH1TangentLinear_rosati A ρ hρ a ((TangentEquiv.polarizedStructureH1TangentEquiv A).symm x)
  change TangentEquiv.polarizedStructureH1TangentEquiv A _ =
    StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a)
      (TangentEquiv.polarizedStructureH1TangentEquiv A ((TangentEquiv.polarizedStructureH1TangentEquiv A).symm x)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem polarizedH1ConormalEquiv_pullback (a : NumberField.RingOfIntegers E)
    (x : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme) :
    polarizedH1ConormalEquiv A (StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a) x) z =
      polarizedH1ConormalEquiv A x
        (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A.abelian ρ (NumberField.IsCMField.ringOfIntegersComplexConj E a) z) := by
  change Intrinsic.IdentityConormalLinear.nativeIdentityConormalLinear A.abelian.scheme
    ((TangentEquiv.polarizedStructureH1TangentEquiv A).symm (StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a) x)) z = _
  rw [polarizedStructureH1TangentEquiv_symm_pullback A ρ hρ]
  exact (Constructed.ConormalIntegralAction.constructedConormalIntegralAction_pairing A.abelian ρ
    (NumberField.IsCMField.ringOfIntegersComplexConj E a) ((TangentEquiv.polarizedStructureH1TangentEquiv A).symm x) z).symm

end

/-! The constructed polarization comparison turns an actual
conormal-to-H1 map into a bilinear form without losing information.
Original CM equivariance becomes its conjugate balancing relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

local instance polarizedBilinearH1Module : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.abelian.scheme
local instance polarizedBilinearIntegral : IsIntegral A.abelian.scheme.left :=
  Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.carrier_integral A.abelian

def polarizedConormalBilinear
    (q : Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) :
    Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ]
      Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ] ℂ :=
  (polarizedH1ConormalEquiv A).toLinearMap.comp q

theorem polarizedConormalBilinear_injective : Function.Injective (polarizedConormalBilinear A) := by
  intro q r h
  apply LinearMap.ext
  intro z
  apply (polarizedH1ConormalEquiv A).injective
  exact LinearMap.congr_fun h z

def polarizedConormalBilinearLinear :
    (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1) →ₗ[ℂ]
      (Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ]
        Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ] ℂ) where
  toFun := polarizedConormalBilinear A
  map_add' q r := LinearMap.ext (fun z => (polarizedH1ConormalEquiv A).map_add (q z) (r z))
  map_smul' c q := LinearMap.ext (fun z => (polarizedH1ConormalEquiv A).map_smul c (q z))

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) (hρ : ActionData.RosatiConjugation A ρ)
    (q : Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left) 1)

include hρ

theorem polarizedConormalBilinear_balanced
    (hq : ∀ a, q.comp (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A.abelian ρ a) =
      (StructurePullbackLinear.nativeStructureH1PullbackLinear (ρ.map a)).comp q)
    (a : NumberField.RingOfIntegers E) (z w : Constructed.IdentityConormal.constructedIdentityConormal ℂ A.abelian.scheme) :
    polarizedConormalBilinear A q (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A.abelian ρ a z) w =
      polarizedConormalBilinear A q z
        (Constructed.ConormalIntegralAction.constructedConormalIntegralAction A.abelian ρ (NumberField.IsCMField.ringOfIntegersComplexConj E a) w) :=
  (congrArg (fun x => polarizedH1ConormalEquiv A x w) (LinearMap.congr_fun (hq a) z)).trans
    (polarizedH1ConormalEquiv_pullback A ρ hρ a (q z) w)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.ConormalBilinear
