import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomUnit
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent

/-! # Hom Local Trivialization -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomLocalTrivialization.Construction

noncomputable section

/-! Coordinates for local Hom sheaves in line-bundle trivializations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def overTrivializationRestrict {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    (hVU : V ≤ U) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hVU)).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE hVU)).mapIso e ≪≫
      SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE hVU)

def localHomCoordinateEquiv {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hVU : V ≤ U) : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N V ≃ Γ(X, V) :=
  (ModuleHomSheaf.Construction.moduleHomOverEquiv M N V).trans
    (((overTrivializationRestrict hVU eM).homCongr (overTrivializationRestrict hVU eN)).trans
      ((SheafOfModules.unitHomEquiv (SheafOfModules.unit (X.ringCatSheaf.over V))).trans
        (SheafHomUnit.Construction.moduleOverSectionsEquiv (LineBundle.Construction.structureSheafModule X) V)))

theorem localHomCoordinateEquiv_apply {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hVU : V ≤ U) (q : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N V) :
    localHomCoordinateEquiv eM eN V hVU q =
      (eN.hom.val.app (.op (Over.mk (homOfLE hVU))))
        (q.1.app (.op (Over.mk (𝟙 V)))
          ((eM.inv.val.app (.op (Over.mk (homOfLE hVU)))) (1 : Γ(X, V)))) := rfl

def localHomCoordinateLinearMap {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hVU : V ≤ U) :
    ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N V →ₗ[Γ(X, V)] Γ(X, V) where
  toFun := localHomCoordinateEquiv eM eN V hVU
  map_add' q q' := (eN.hom.val.app (.op (Over.mk (homOfLE hVU)))).hom.map_add _ _
  map_smul' r q := by
    let g : Γ(M, V) := (eM.inv.val.app (.op (Over.mk (homOfLE hVU)))) (1 : Γ(X, V))
    let z : Γ(N, V) := q.1.app (.op (Over.mk (𝟙 V))) g
    let y : Γ(X, V) := (eN.hom.val.app (.op (Over.mk (homOfLE hVU)))) z
    change (eN.hom.val.app (.op (Over.mk (homOfLE hVU))))
        (X.presheaf.map (𝟙 V).op r • z) = r * y
    have h : (eN.hom.val.app (.op (Over.mk (homOfLE hVU)))) (r • z) = r * y :=
      (eN.hom.val.app (.op (Over.mk (homOfLE hVU)))).hom.map_smul r z
    have h₁ : X.presheaf.map (𝟙 V).op r = r := by simp
    exact (congrArg (fun a ↦ (eN.hom.val.app (.op (Over.mk (homOfLE hVU)))) (a • z)) h₁).trans h

def localHomCoordinateLinearEquiv {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hVU : V ≤ U) :
    ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  LinearEquiv.ofBijective (localHomCoordinateLinearMap eM eN V hVU)
    (localHomCoordinateEquiv eM eN V hVU).bijective

theorem localHomCoordinate_restrict {X : Scheme.{u}} {M N : X.Modules} {U V W : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hVU : V ≤ U) (hWV : W ≤ V) (q : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N V) :
    localHomCoordinateEquiv eM eN W (hWV.trans hVU)
        ((ModuleHomAdditive.Construction.moduleHomAbPresheaf M N).map (homOfLE hWV).op q) =
      X.presheaf.map (homOfLE hWV).op (localHomCoordinateEquiv eM eN V hVU q) := by
  let v : Over U := Over.mk (homOfLE hVU)
  let w : Over U := Over.mk (homOfLE (hWV.trans hVU))
  let j : w ⟶ v := Over.homMk (homOfLE hWV)
  let gV : Γ(M, V) := eM.inv.val.app (.op v) (1 : Γ(X, V))
  let gW : Γ(M, W) := eM.inv.val.app (.op w) (1 : Γ(X, W))
  have hm := PresheafOfModules.naturality_apply eM.inv.val j.op (1 : Γ(X, V))
  have hg : M.presheaf.map (homOfLE hWV).op gV = gW := by
    exact hm.symm.trans (congrArg (fun a ↦ eM.inv.val.app (.op w) a)
      ((X.presheaf.map (homOfLE hWV).op).hom.map_one))
  let k : Over.mk (homOfLE hWV) ⟶ Over.mk (𝟙 V) := Over.homMk (homOfLE hWV)
  have hq := congrArg (fun a ↦ a gV) (q.1.naturality k.op)
  have hn := PresheafOfModules.naturality_apply eN.hom.val j.op
    (q.1.app (.op (Over.mk (𝟙 V))) gV)
  change eN.hom.val.app (.op w) (q.1.app (.op (Over.mk (homOfLE hWV))) gW) = _
  exact (congrArg (fun a ↦ eN.hom.val.app (.op w)
      (q.1.app (.op (Over.mk (homOfLE hWV))) a)) hg).symm.trans
    ((congrArg (fun a ↦ eN.hom.val.app (.op w) a) hq).trans hn)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomLocalTrivialization.Construction
