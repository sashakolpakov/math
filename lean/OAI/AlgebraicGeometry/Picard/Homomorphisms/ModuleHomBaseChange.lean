import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames

/-! # Module Hom Base Change -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomBaseChange

noncomputable section

/-! Base change of a compatible module morphism, retaining its ordinary
descent datum through the native pseudofunctor comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def nativeDescentEvaluation :
    PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f) ⥤ X.Modules where
  obj D := D.obj PUnit.unit
  map b := b.hom PUnit.unit

def nativeDescentHom
    (D E : PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (b : (IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D).module ⟶
      (IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f E).module)
    (hb : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x).map b ≫ (IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f E).hom q x y hx hy =
        (IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D).hom q x y hx hy ≫
          (Scheme.Modules.pullback y).map b) : D ⟶ E where
  hom i := by cases i; exact b
  comm T q i j x y hx hy := by
    cases i
    cases j
    exact hb q x y hx hy

def canonicalDescentHom {L M : Y.Modules}
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    (hb : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x).map b ≫ (CanonicalDescentFrames.Construction.canonicalModuleDescent f M).hom q x y hx hy =
        (CanonicalDescentFrames.Construction.canonicalModuleDescent f L).hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b) :
    (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M :=
  nativeDescentHom f _ _ b hb

def canonicalDescentModuleHom {L M : Y.Modules}
    (b : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :
    (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M :=
  b.hom PUnit.unit

variable {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (s : Y' ⟶ Y) (t : X' ⟶ X)
variable (w : t ≫ f = f' ≫ s)

def descentSquareFunctor :
    PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f) ⥤
      PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f') :=
  Pseudofunctor.DescentData.pullFunctor PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    (α := id) (p := s) (p' := fun _ => t) (fun _ => w)

def descentSquareComparison :
    PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f) ⋙ descentSquareFunctor f f' s t w ≅
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.map s.op.toLoc).toFunctor ⋙
        PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f') :=
  Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso PoincareBundle.Geometric.KernelLinearization.modulePullbacks
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f')
    (α := id) (p := s) (p' := fun _ => t) (fun _ => w)

def moduleDescentSquareIso (L : Y.Modules) :
    (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback f).obj L) ≅
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback s).obj L) :=
  (nativeDescentEvaluation f').mapIso ((descentSquareComparison f f' s t w).app L)

def baseChangedDescentHom {L M : Y.Modules}
    (b : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :
    (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f')).obj
        ((Scheme.Modules.pullback s).obj L) ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f')).obj
        ((Scheme.Modules.pullback s).obj M) :=
  ((descentSquareComparison f f' s t w).app L).inv ≫
    (descentSquareFunctor f f' s t w).map b ≫ ((descentSquareComparison f f' s t w).app M).hom

theorem baseChangedDescentHom_component {L M : Y.Modules}
    (b : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :
    (baseChangedDescentHom f f' s t w b).hom PUnit.unit =
      (moduleDescentSquareIso f f' s t w L).inv ≫
        (Scheme.Modules.pullback t).map (b.hom PUnit.unit) ≫
          (moduleDescentSquareIso f f' s t w M).hom := rfl

def nativeModuleDescentSquareIso :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback t ≅
      Scheme.Modules.pullback s ⋙ Scheme.Modules.pullback f' :=
  Scheme.Modules.pullbackComp t f ≪≫
    (Scheme.Modules.pullbackComp f' s ≪≫ Scheme.Modules.pullbackCongr w.symm).symm

theorem moduleDescentSquareIso_eq (L : Y.Modules) :
    moduleDescentSquareIso f f' s t w L = (nativeModuleDescentSquareIso f f' s t w).app L := by
  apply Iso.ext
  change (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.isoMapOfCommSq (CommSq.mk w).op.toLoc).inv.toNatTrans.app L = _
  rw [PoincareBundle.Geometric.KernelLinearization.modulePullbacks.isoMapOfCommSq_eq (CommSq.mk w).op.toLoc (t ≫ f).op.toLoc
    (congrArg (fun a : X' ⟶ Y => a.op.toLoc) w.symm)]
  change (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.mapComp' f.op.toLoc t.op.toLoc (t ≫ f).op.toLoc rfl).inv.toNatTrans.app L ≫
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.mapComp' s.op.toLoc f'.op.toLoc (t ≫ f).op.toLoc
        (congrArg (fun a : X' ⟶ Y => a.op.toLoc) w.symm)).hom.toNatTrans.app L = _
  rw [CanonicalDescentFrames.Construction.modulePullbacks_mapComp_inv f L (t ≫ f) t rfl,
    CanonicalDescentFrames.Construction.modulePullbacks_mapComp_hom s L (t ≫ f) f' w.symm]
  rfl

theorem baseChangedDescentHom_native {L M : Y.Modules}
    (b : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :
    (baseChangedDescentHom f f' s t w b).hom PUnit.unit =
      ((nativeModuleDescentSquareIso f f' s t w).app L).inv ≫
        (Scheme.Modules.pullback t).map (b.hom PUnit.unit) ≫
          ((nativeModuleDescentSquareIso f f' s t w).app M).hom := by
  rw [baseChangedDescentHom_component, moduleDescentSquareIso_eq, moduleDescentSquareIso_eq]

theorem baseChangedDescentHom_map {L M : Y.Modules} (a : L ⟶ M) :
    baseChangedDescentHom f f' s t w
      ((PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).map a) =
        (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f')).map
          ((Scheme.Modules.pullback s).map a) := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  cases i
  rw [baseChangedDescentHom_component, moduleDescentSquareIso_eq, moduleDescentSquareIso_eq]
  exact NatIso.naturality_1 (nativeModuleDescentSquareIso f f' s t w) a

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomBaseChange
