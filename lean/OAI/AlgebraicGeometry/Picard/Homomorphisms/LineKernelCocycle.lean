import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar

/-! # Line Kernel Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle

noncomputable section

/-! A line bundle trivialized by a group morphism supplies an actual
scalar cocycle for the scheme-theoretic kernel action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]

theorem kernel_translate_comp {T : Over S} (x : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) :
    (x * (z ≫ Kernel.Construction.kernelInclusion f)) ≫ f = x ≫ f := by
  rw [MonObj.mul_comp, Category.assoc, KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one, mul_one]

variable (D : IntrinsicModuleDescent.Construction.NativeModuleDescent f.left) (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)

def framedKernelScalar {T : Over S} (x : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) : Γ(T.left, ⊤) :=
  FramedDescentScalars.Construction.framedDescentScalar D e (x ≫ f).left x.left (x * (z ≫ Kernel.Construction.kernelInclusion f)).left rfl
    (congrArg Over.Hom.left (kernel_translate_comp f x z))

theorem framedKernelScalar_naturality {T T' : Over S} (t : T' ⟶ T)
    (x : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) :
    t.left.appTop (framedKernelScalar f D e x z) =
      framedKernelScalar f D e (t ≫ x) (t ≫ z) := by
  have h := FramedDescentScalars.Construction.framedDescentScalar_pullback D e t.left (x ≫ f).left x.left
    (x * (z ≫ Kernel.Construction.kernelInclusion f)).left rfl
      (congrArg Over.Hom.left (kernel_translate_comp f x z))
  simp only [← Over.comp_left, MonObj.comp_mul] at h
  exact h

theorem framedKernelScalar_unit {T : Over S} (x : T ⟶ A) :
    framedKernelScalar f D e x 1 = 1 := by
  unfold framedKernelScalar
  simp only [MonObj.one_comp, mul_one]
  exact FramedDescentScalars.Construction.framedDescentScalar_self D e _ _ _

theorem framedKernelScalar_cocycle {T : Over S} (x : T ⟶ A)
    (z w : T ⟶ Kernel.Construction.kernelScheme f) :
    framedKernelScalar f D e x z * framedKernelScalar f D e (x * (z ≫ Kernel.Construction.kernelInclusion f)) w =
      framedKernelScalar f D e x (z * w) := by
  let y := x * (z ≫ Kernel.Construction.kernelInclusion f)
  let z' := y * (w ≫ Kernel.Construction.kernelInclusion f)
  have hy : y ≫ f = x ≫ f := kernel_translate_comp f x z
  have hz : z' ≫ f = x ≫ f := (kernel_translate_comp f y w).trans hy
  have hend : z' = x * ((z * w) ≫ Kernel.Construction.kernelInclusion f) := by
    dsimp [z', y]
    rw [MonObj.mul_comp, mul_assoc]
  have hy' := congrArg Over.Hom.left hy
  have hz' := congrArg Over.Hom.left hz
  have h₂ : framedKernelScalar f D e y w =
      FramedDescentScalars.Construction.framedDescentScalar D e (x ≫ f).left y.left z'.left hy' hz' :=
    FramedDescentScalars.Construction.framedDescentScalar_congr D e _ _ _ _ _ _ _ _ _ _ hy' rfl rfl
  have h₃ : FramedDescentScalars.Construction.framedDescentScalar D e (x ≫ f).left x.left z'.left rfl hz' =
      framedKernelScalar f D e x (z * w) :=
    FramedDescentScalars.Construction.framedDescentScalar_congr D e _ _ _ _ _ _ _ _ _ _ rfl rfl (congrArg Over.Hom.left hend)
  exact (congrArg (fun a => framedKernelScalar f D e x z * a) h₂).trans
    ((FramedDescentScalars.Construction.framedDescentScalar_comp D e (x ≫ f).left x.left y.left z'.left rfl hy' hz').trans h₃)

def framedKernelScalarCocycle : KernelScalar.Construction.KernelScalarCocycle f where
  value := framedKernelScalar f D e
  isUnit _ _ := FramedDescentScalars.Construction.framedDescentScalar_isUnit D e _ _ _ _ _
  naturality := framedKernelScalar_naturality f D e
  unit := framedKernelScalar_unit f D e
  cocycle := framedKernelScalar_cocycle f D e

def pullbackLineNativeDatum (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) : IntrinsicModuleDescent.Construction.NativeModuleDescent f.left :=
  IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f.left
    ((PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f.left)).obj L.sheaf)

def pullbackLineKernelCocycle (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (e : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) :
    KernelScalar.Construction.KernelScalarCocycle f :=
  framedKernelScalarCocycle f (pullbackLineNativeDatum f L) e

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineKernelCocycle
