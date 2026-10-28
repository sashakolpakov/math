import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCharacters
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelBaseChange

/-! # Kernel Character Detection -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection

noncomputable section

/-! The kernel character retains the full original descent datum on all
test schemes, including nonreduced schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]

theorem kernel_action_covers_relation {T : Over S} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    ∃ z : T ⟶ Kernel.Construction.kernelScheme f, x * (z ≫ Kernel.Construction.kernelInclusion f) = y := by
  let z := FrobeniusKernelBaseChange.Construction.kernelLift f (x⁻¹ * y) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, inv_mul_cancel])
  refine ⟨z, ?_⟩
  rw [show z ≫ Kernel.Construction.kernelInclusion f = x⁻¹ * y from FrobeniusKernelBaseChange.Construction.kernelLift_inclusion _ _ _, mul_inv_cancel_left]

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable {f : A ⟶ B} [IsMonHom f]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable [IsAffine (Kernel.Construction.kernelScheme f).left]
variable (D E : IntrinsicModuleDescent.Construction.NativeModuleDescent f.left)
variable (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) (d : E.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)

theorem kernelScalar_eq_implies_descentScalar_eq
    (h : (LineKernelCocycle.Construction.framedKernelScalarCocycle f D e).kernelScalar =
      (LineKernelCocycle.Construction.framedKernelScalarCocycle f E d).kernelScalar)
    {T : Over (Spec (.of k))} (x y : T ⟶ A) (hxy : x ≫ f = y ≫ f) :
    FramedDescentScalars.Construction.framedDescentScalar D e (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) =
      FramedDescentScalars.Construction.framedDescentScalar E d (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) := by
  obtain ⟨z, hz⟩ := kernel_action_covers_relation f x y hxy
  have hd := (LineKernelCocycle.Construction.framedKernelScalarCocycle f D e).value_eq_kernelScalar x z
  have he := (LineKernelCocycle.Construction.framedKernelScalarCocycle f E d).value_eq_kernelScalar x z
  have hc : LineKernelCocycle.Construction.framedKernelScalar f D e x z = LineKernelCocycle.Construction.framedKernelScalar f E d x z :=
    hd.trans ((congrArg z.left.appTop h).trans he.symm)
  have hD : LineKernelCocycle.Construction.framedKernelScalar f D e x z =
      FramedDescentScalars.Construction.framedDescentScalar D e (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) :=
    FramedDescentScalars.Construction.framedDescentScalar_congr D e _ _ _ _ _ _ _ _ _ _ rfl rfl (congrArg Over.Hom.left hz)
  have hE : LineKernelCocycle.Construction.framedKernelScalar f E d x z =
      FramedDescentScalars.Construction.framedDescentScalar E d (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) :=
    FramedDescentScalars.Construction.framedDescentScalar_congr E d _ _ _ _ _ _ _ _ _ _ rfl rfl (congrArg Over.Hom.left hz)
  exact hD.symm.trans (hc.trans hE)

theorem kernelScalar_eq_implies_native_compatible
    (h : (LineKernelCocycle.Construction.framedKernelScalarCocycle f D e).kernelScalar =
      (LineKernelCocycle.Construction.framedKernelScalarCocycle f E d).kernelScalar)
    {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    (Scheme.Modules.pullback x).map (e.hom ≫ d.inv) ≫ E.hom q x y hx hy =
      D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map (e.hom ≫ d.inv) := by
  let T' : Over (Spec (.of k)) := Over.mk (x ≫ A.hom)
  let x' : T' ⟶ A := Over.homMk x rfl
  let y' : T' ⟶ A := Over.homMk y (by
    change y ≫ A.hom = x ≫ A.hom
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hx, hy])
  have hxy : x' ≫ f = y' ≫ f := Over.OverMorphism.ext (hx.trans hy.symm)
  have hs := kernelScalar_eq_implies_descentScalar_eq D E e d h x' y' hxy
  have hD := FramedDescentScalars.Construction.framedDescentScalar_congr D e (x' ≫ f).left q x'.left x y'.left y
    rfl (congrArg Over.Hom.left hxy.symm) hx hy hx rfl rfl
  have hE := FramedDescentScalars.Construction.framedDescentScalar_congr E d (x' ≫ f).left q x'.left x y'.left y
    rfl (congrArg Over.Hom.left hxy.symm) hx hy hx rfl rfl
  exact FramedDescentComparison.Construction.framedDescentScalar_eq_implies_compatible D E e d q x y hx hy
    (hD.symm.trans (hs.trans hE))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection
