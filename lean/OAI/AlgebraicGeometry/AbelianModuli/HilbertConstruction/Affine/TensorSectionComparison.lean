import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionModules
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPushoutTensorComparison

/-! # Tensor Section Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorSectionComparison

noncomputable section

/-! The tensor comparison is bijective on affine opens after affine base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y P : Scheme.{u}}

def morphismGlobalAlgebra (g : Y ⟶ S) : CommAlgCat.{u} Γ(S, ⊤) :=
  letI := g.appTop.hom.toAlgebra
  .of Γ(S, ⊤) Γ(Y, ⊤)

theorem cartesianGlobalCoefficient_compatibility
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g) :
    b.appTop.hom.comp (algebraMap Γ(S, ⊤) (morphismGlobalAlgebra g)) =
      a.appTop.hom.comp f.appTop.hom := by
  have h := congrArg (fun k : P ⟶ S => k.appTop) H.w
  simp only [Scheme.Hom.comp_appTop] at h
  exact congrArg CommRingCat.Hom.hom h.symm

def baseChangeTensorSectionComparison
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g) :=
  Tensor.SectionModules.tensorSectionModuleComparison a f.appTop.hom (morphismGlobalAlgebra g) b.appTop.hom
    (cartesianGlobalCoefficient_compatibility H)

theorem affineOpen_tensorComparison_bijective [IsAffine S] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Bijective ((baseChangeTensorSectionComparison H).app (.op U)) := by
  let B := morphismGlobalAlgebra g
  let A := Coefficient.AlgebraPresheaf.coefficientAlgebraSections f.appTop.hom U
  let C := Coefficient.AlgebraPresheaf.coefficientAlgebraSections (a.appTop.hom.comp f.appTop.hom) (a ⁻¹ᵁ U)
  let i : B →ₐ[Γ(S, ⊤)] C :=
    (Coefficient.AlgebraPullback.coefficientAlgebraGlobalRestriction _ B b.appTop.hom
      (cartesianGlobalCoefficient_compatibility H) (a ⁻¹ᵁ U)).hom
  let j : A →ₐ[Γ(S, ⊤)] C := (Coefficient.AlgebraPullback.coefficientAlgebraPullbackApp a f.appTop.hom U).hom
  have h : IsPushout (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B))
      (CommRingCat.ofHom (algebraMap Γ(S, ⊤) A))
      (CommRingCat.ofHom i.toRingHom) (CommRingCat.ofHom j.toRingHom) :=
    (Open.FunctionsBaseChange.affineOpen_isPushout_functions H U hU).flip
  exact RingPushoutTensorComparison.tensorLift_bijective_of_isPushout i j h

theorem affineOpen_tensorComparison_isIso [IsAffine S] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso ((baseChangeTensorSectionComparison H).app (.op U)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (affineOpen_tensorComparison_bijective H U hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorSectionComparison
