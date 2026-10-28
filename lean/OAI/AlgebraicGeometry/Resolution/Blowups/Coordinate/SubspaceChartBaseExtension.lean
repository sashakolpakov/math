import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChart

/-! # Subspace Chart Base Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual coordinate charts on an ambient open retain their model and equations over the original ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart.extendBase {X V : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
    (j : V ⟶ X) [IsOpenImmersion j] {x : V}
    (C : Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart (j ≫ f) (J.comap j) x) :
    Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J (j x) where
  ring := C.ring
  algebra := C.algebra
  smooth := C.smooth
  domain := C.domain
  map := C.map ≫ j
  isOpenImmersion := inferInstance
  ground := by rw [Category.assoc]; exact C.ground
  point := C.point
  point_over := by change j (C.map C.point) = j x; rw [C.point_over]
  normal := C.normal
  normalFinite := C.normalFinite
  normalDecidableEq := C.normalDecidableEq
  freeDimension := C.freeDimension
  coordinate := C.coordinate
  coordinate_etale := C.coordinate_etale
  modelNonzero := C.modelNonzero
  ideal_eq := by rw [Scheme.IdealSheafData.comap_comp]; exact C.ideal_eq

end

end OAI.AlgebraicGeometry.Resolution.Blowups
