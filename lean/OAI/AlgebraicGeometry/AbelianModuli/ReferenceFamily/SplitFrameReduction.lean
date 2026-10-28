import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

/-! # Split Frame Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitFrameReduction

noncomputable section

section

/-! Transition units formed from actual module-sheaf frames, with
their cocycle equation and arbitrary scheme-pullback compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable {X Y : Scheme.{0}} {M : X.Modules}

def lineFrameTransitionUnit (e f : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) : Γ(X, ⊤)ˣ :=
  Isogenies.NeighborCounting.ModuleScalar.structureAutUnit (f.symm ≪≫ e)

theorem lineFrameTransitionUnit_val (e f : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    (lineFrameTransitionUnit e f).val = Isogenies.NeighborCounting.FramedHom.framedCoefficient f e (𝟙 M) := by
  change ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X (f.inv ≫ e.hom) =
    ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X (f.inv ≫ 𝟙 M ≫ e.hom)
  rw [Category.id_comp]

theorem lineFrameTransitionUnit_self (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    lineFrameTransitionUnit e e = 1 := by
  apply Units.ext
  change ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X (e.inv ≫ e.hom) = 1
  rw [e.inv_hom_id]
  exact map_one (ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X)

theorem lineFrameTransitionUnit_cocycle (e f g : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    lineFrameTransitionUnit e f * lineFrameTransitionUnit f g = lineFrameTransitionUnit e g := by
  apply Units.ext
  change ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X (f.inv ≫ e.hom) *
    ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X (g.inv ≫ f.hom) = ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections.Construction.structureSheafEndRingEquiv X (g.inv ≫ e.hom)
  rw [← map_mul]
  congr 1
  change (g.inv ≫ f.hom) ≫ (f.inv ≫ e.hom) = g.inv ≫ e.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem lineFrameTransitionUnit_pullback (e f : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (r : Y ⟶ X) :
    Units.map r.appTop.hom.toMonoidHom (lineFrameTransitionUnit e f) =
      lineFrameTransitionUnit (Isogenies.NeighborCounting.FramedHom.pullbackFrame r e) (Isogenies.NeighborCounting.FramedHom.pullbackFrame r f) := by
  apply Units.ext
  change r.appTop (lineFrameTransitionUnit e f).val =
    (lineFrameTransitionUnit (Isogenies.NeighborCounting.FramedHom.pullbackFrame r e) (Isogenies.NeighborCounting.FramedHom.pullbackFrame r f)).val
  rw [lineFrameTransitionUnit_val, lineFrameTransitionUnit_val]
  have h := Isogenies.NeighborCounting.FramedHom.framedCoefficient_pullback f e r (𝟙 M)
  rw [CategoryTheory.Functor.map_id] at h
  exact h.symm

theorem lineFrameTransitionUnit_reduction (e f : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (r : Y ⟶ X)
    (h : Isogenies.NeighborCounting.FramedHom.pullbackFrame r e = Isogenies.NeighborCounting.FramedHom.pullbackFrame r f) :
    Units.map r.appTop.hom.toMonoidHom (lineFrameTransitionUnit e f) = 1 := by
  rw [lineFrameTransitionUnit_pullback, h, lineFrameTransitionUnit_self]

end

section

/-! A prescribed frame on a split reduction lifts to an actual frame
whenever the original module is already framed. The lift is constructed
by pulling back the exact transition unit along the retraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable {X Y : Scheme.{0}} {M : Y.Modules}

theorem lineFrameTransitionUnit_reconstruct
    (e f : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) :
    e ≪≫ Isogenies.NeighborCounting.ModuleScalar.scalarIso (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) (lineFrameTransitionUnit f e) = f := by
  apply Iso.ext
  change e.hom ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)
    (Isogenies.NeighborCounting.ModuleScalar.structureAutUnit (e.symm ≪≫ f)).val = f.hom
  rw [Isogenies.NeighborCounting.ModuleScalar.scalarEnd_structureAut]
  exact e.hom_inv_id_assoc f.hom

theorem pullbackFrame_scalar (r : X ⟶ Y) (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) (u : Γ(Y, ⊤)ˣ) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame r (e ≪≫ Isogenies.NeighborCounting.ModuleScalar.scalarIso (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) u) =
      Isogenies.NeighborCounting.FramedHom.pullbackFrame r e ≪≫ Isogenies.NeighborCounting.ModuleScalar.scalarIso (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (Units.map r.appTop.hom.toMonoidHom u) := by
  apply Iso.ext
  change (Scheme.Modules.pullback r).map (e.hom ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y) u.val) ≫
      (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso r).hom =
    ((Scheme.Modules.pullback r).map e.hom ≫ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso r).hom) ≫
      Isogenies.NeighborCounting.ModuleScalar.scalarEnd (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (r.appTop u.val)
  rw [CategoryTheory.Functor.map_comp, Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback, Category.assoc,
    Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality, Category.assoc]

theorem unit_pullback_retraction (r : X ⟶ Y) (p : Y ⟶ X) (h : r ≫ p = 𝟙 X) (u : Γ(X, ⊤)ˣ) :
    Units.map r.appTop.hom.toMonoidHom (Units.map p.appTop.hom.toMonoidHom u) = u := by
  apply Units.ext
  change r.appTop (p.appTop u.val) = u.val
  have he := congrArg (fun f : X ⟶ X => f.appTop u.val) h
  exact he

def splitReductionFrameLift (r : X ⟶ Y) (p : Y ⟶ X)
    (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)
    (f : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y :=
  e ≪≫ Isogenies.NeighborCounting.ModuleScalar.scalarIso (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)
    (Units.map p.appTop.hom.toMonoidHom (lineFrameTransitionUnit f (Isogenies.NeighborCounting.FramedHom.pullbackFrame r e)))

theorem splitReductionFrameLift_reduces (r : X ⟶ Y) (p : Y ⟶ X) (h : r ≫ p = 𝟙 X)
    (e : M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)
    (f : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame r (splitReductionFrameLift r p e f) = f := by
  rw [splitReductionFrameLift, pullbackFrame_scalar, unit_pullback_retraction r p h]
  exact lineFrameTransitionUnit_reconstruct (Isogenies.NeighborCounting.FramedHom.pullbackFrame r e) f

end

/-! A change of reduced global frame lifts to an actual scalar
automorphism of the unframed module along a split reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

theorem scalarIso_pullback {X Y : Scheme.{0}} (r : X ⟶ Y) (M : Y.Modules) (u : Γ(Y, ⊤)ˣ) :
    (Scheme.Modules.pullback r).mapIso (Isogenies.NeighborCounting.ModuleScalar.scalarIso M u) =
      Isogenies.NeighborCounting.ModuleScalar.scalarIso ((Scheme.Modules.pullback r).obj M) (Units.map r.appTop.hom.toMonoidHom u) := by
  apply Iso.ext
  exact Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback r M u.val

theorem scalarIso_naturality {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N) (u : Γ(X, ⊤)ˣ) :
    Isogenies.NeighborCounting.ModuleScalar.scalarIso M u ≪≫ e = e ≪≫ Isogenies.NeighborCounting.ModuleScalar.scalarIso N u := by
  apply Iso.ext
  exact Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality e.hom u.val

def splitReductionFrameAut {X Y : Scheme.{0}} (r : X ⟶ Y) (p : Y ⟶ X) {M : Y.Modules}
    (e d : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) : M ≅ M :=
  Isogenies.NeighborCounting.ModuleScalar.scalarIso M (Units.map p.appTop.hom.toMonoidHom (lineFrameTransitionUnit d e))

theorem splitReductionFrameAut_reduces {X Y : Scheme.{0}} (r : X ⟶ Y) (p : Y ⟶ X)
    (h : r ≫ p = 𝟙 X) {M : Y.Modules}
    (e d : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    (Scheme.Modules.pullback r).mapIso (splitReductionFrameAut r p e d) ≪≫ e = d := by
  have h₁ := congrArg (fun q => q ≪≫ e) (scalarIso_pullback r M
    (Units.map p.appTop.hom.toMonoidHom (lineFrameTransitionUnit d e)))
  have h₂ := scalarIso_naturality e
    (Units.map r.appTop.hom.toMonoidHom (Units.map p.appTop.hom.toMonoidHom (lineFrameTransitionUnit d e)))
  have h₃ := congrArg (fun u => e ≪≫ Isogenies.NeighborCounting.ModuleScalar.scalarIso (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) u)
    (unit_pullback_retraction r p h (lineFrameTransitionUnit d e))
  exact h₁.trans (h₂.trans (h₃.trans (lineFrameTransitionUnit_reconstruct e d)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitFrameReduction
