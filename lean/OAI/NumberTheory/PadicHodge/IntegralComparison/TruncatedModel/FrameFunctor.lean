import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrameMorphism
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingExt

/-! # Frame Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor

noncomputable section

/-! The actual affine sections of a smooth finite-level model form a
strict functor into the original bounded crystalline site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "AU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X U
local notation "AV" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X V
local notation "CU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f U
local notation "CV" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X Y f V

local instance sourceU : Algebra S AU := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U
local instance sourceV : Algebra S AV := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X V
local instance residueU : Algebra k CU := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ U)
local instance residueV : Algebra k CV := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y (f ⁻¹ᵁ V)

def integralMap : AV →ₐ[S] AU := ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras S X).map (homOfLE hUV).op).hom

def residueMap : CV →ₐ[k] CU :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y).map
    (((TopologicalSpace.Opens.map f.base).map (homOfLE hUV)).op)).hom

omit [Fintype k] [CharP k p] [Smooth X.hom] in
theorem reduction_square (a : AV) :
    Truncated.AffineModelFrame.reduction p k n X Y f U (integralMap p k n X U V hUV a) =
      residueMap p k n X Y f U V hUV (Truncated.AffineModelFrame.reduction p k n X Y f V a) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE hUV).op) a

def geometricMap : Spec CU ⟶ Spec CV := Spec.map (CommRingCat.ofHom (residueMap p k n X Y f U V hUV).toRingHom)

omit [Smooth X.hom] in
theorem chart_square : geometricMap p k n X Y f U V hUV ≫
    Truncated.AffineModelFrame.chart p k n X Y f hp V hV =
      Truncated.AffineModelFrame.chart p k n X Y f hp U hU :=
  (Truncated.AffineModelFrame.residue_affine p k n X Y f hp V hV).map_fromSpec
    (Truncated.AffineModelFrame.residue_affine p k n X Y f hp U hU)
    (((TopologicalSpace.Opens.map f.base).map (homOfLE hUV)).op)

def localMap :
    (BoundedOpen.Equivalence.postcompose (geometricMap p k n X Y f U V hUV)
      (Truncated.SmoothFrameMorphism.base_square p k CV CU (residueMap p k n X Y f U V hUV)) n).obj
        (Truncated.AffineModelFrame.localFrame p k n X Y f hp U hU) ⟶
      Truncated.AffineModelFrame.localFrame p k n X Y f hp V hV := by
  letI := Truncated.AffineModelFrame.source_smooth p k n X U hU
  letI := Truncated.AffineModelFrame.source_smooth p k n X V hV
  exact Truncated.SmoothFrameMorphism.boundedMorphism p k n AV AU (integralMap p k n X U V hUV) CV CU
    (Truncated.AffineModelFrame.reduction p k n X Y f V)
    (Truncated.AffineModelFrame.reduction_surjective p k n X Y f hp V hV)
    (Truncated.AffineModelFrame.reduction_kernel p k n X Y f hp V hV)
    (Truncated.AffineModelFrame.reduction_base p k n X Y f hp V hV)
    (Truncated.AffineModelFrame.reduction p k n X Y f U)
    (Truncated.AffineModelFrame.reduction_surjective p k n X Y f hp U hU)
    (Truncated.AffineModelFrame.reduction_kernel p k n X Y f hp U hU)
    (Truncated.AffineModelFrame.reduction_base p k n X Y f hp U hU)
    (residueMap p k n X Y f U V hUV) (reduction_square p k n X Y f U V hUV)

def map : Truncated.AffineModelFrame.frame p k n X Y f hp U hU ⟶
    Truncated.AffineModelFrame.frame p k n X Y f hp V hV :=
  ObjectProperty.homMk {
    ringMap := (localMap p k n X Y f hp U V hU hV hUV).hom.ringMap
    overBase := (localMap p k n X Y f hp U V hU hV hUV).hom.overBase
    overX := by
      let α := (localMap p k n X Y f hp U V hU hV hUV).hom
      let jV := Truncated.AffineModelFrame.chart p k n X Y f hp V hV
      let jU := Truncated.AffineModelFrame.chart p k n X Y f hp U hU
      let cU := (Truncated.AffineModelFrame.localFrame p k n X Y f hp U hU).obj.mapToX
      change BigCrystallineSite.Object.closed.map α ≫
        ((Truncated.AffineModelFrame.localFrame p k n X Y f hp V hV).obj.mapToX ≫ jV) = cU ≫ jU
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ jV) α.overX).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun m => cU ≫ m) (chart_square p k n X Y f hp U V hU hV hUV)))) }

theorem map_ringMap : (FrameFunctor.map p k n X Y f hp U V hU hV hUV).hom.ringMap =
    (localMap p k n X Y f hp U V hU hV hUV).hom.ringMap := rfl

theorem map_apply (a : AV) :
    (FrameFunctor.map p k n X Y f hp U V hU hV hUV).hom.ringMap a = integralMap p k n X U V hUV a := by
  rw [map_ringMap]
  rfl

omit [Fintype k] [CharP k p] [Smooth X.hom] in
theorem integral_id (a : AU) : integralMap p k n X U U le_rfl a = a := by
  change (X.left.presheaf.map (𝟙 (op U))).hom a = a
  rw [X.left.presheaf.map_id]
  rfl

omit [Fintype k] [CharP k p] [Smooth X.hom] in
theorem integral_comp (T : X.left.Opens) (hVT : V ≤ T) (a : Γ(X.left, T)) :
    integralMap p k n X U T (hUV.trans hVT) a =
      integralMap p k n X U V hUV (integralMap p k n X V T hVT a) := by
  change (X.left.presheaf.map (homOfLE (hUV.trans hVT)).op).hom a =
    (X.left.presheaf.map (homOfLE hUV).op).hom ((X.left.presheaf.map (homOfLE hVT).op).hom a)
  rw [show (homOfLE (hUV.trans hVT)).op = (homOfLE hVT).op ≫ (homOfLE hUV).op from Subsingleton.elim _ _,
    X.left.presheaf.map_comp]
  rfl

theorem map_id : FrameFunctor.map p k n X Y f hp U U hU hU le_rfl =
    𝟙 (Truncated.AffineModelFrame.frame p k n X Y f hp U hU) := by
  exact GeometricComparison.BoundedFrame.RingExt.BoundedFrameRingExt.id_of_formula (fun a : AU => a) (fun a => ⟨a, rfl⟩)
    (FrameFunctor.map p k n X Y f hp U U hU hU le_rfl) (integralMap p k n X U U le_rfl)
    (map_apply p k n X Y f hp U U hU hU le_rfl) (integral_id p k n X U)

theorem map_comp (T : X.left.Opens) (hT : IsAffineOpen T) (hVT : V ≤ T) :
    FrameFunctor.map p k n X Y f hp U T hU hT (hUV.trans hVT) =
      FrameFunctor.map p k n X Y f hp U V hU hV hUV ≫ FrameFunctor.map p k n X Y f hp V T hV hT hVT := by
  exact GeometricComparison.BoundedFrame.RingExt.BoundedFrameRingExt.comp_of_formulas (fun a : AU => a) (fun a : AV => a)
    (fun a : Γ(X.left, T) => a) (fun a => ⟨a, rfl⟩)
    (FrameFunctor.map p k n X Y f hp U V hU hV hUV) (FrameFunctor.map p k n X Y f hp V T hV hT hVT)
    (FrameFunctor.map p k n X Y f hp U T hU hT (hUV.trans hVT))
    (integralMap p k n X U V hUV) (integralMap p k n X V T hVT)
    (integralMap p k n X U T (hUV.trans hVT))
    (map_apply p k n X Y f hp U V hU hV hUV) (map_apply p k n X Y f hp V T hV hT hVT)
    (map_apply p k n X Y f hp U T hU hT (hUV.trans hVT)) (integral_comp p k n X U V hUV T hVT)

def functor : X.left.affineOpens ⥤ BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n where
  obj U := Truncated.AffineModelFrame.frame p k n X Y f hp U.val U.property
  map {U V} α := FrameFunctor.map p k n X Y f hp U.val V.val U.property V.property (leOfHom α)
  map_id U := FrameFunctor.map_id p k n X Y f hp U.val U.property
  map_comp {U V T} α β := FrameFunctor.map_comp p k n X Y f hp U.val V.val U.property V.property
    (leOfHom α) T.val T.property (leOfHom β)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor
