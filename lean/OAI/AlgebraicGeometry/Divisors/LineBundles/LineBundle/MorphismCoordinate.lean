import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame

/-! # Morphism Coordinate -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismCoordinate.Cycles

noncomputable section

/-! The local equation of an actual line-bundle map to the
structure sheaf, expressed in its genuine sheaf frames. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def moduleSectionLinearMap {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun m := φ.app U m
  map_add' m n := (φ.app U).hom.map_add m n
  map_smul' r m := by simpa only [RingHom.id_apply] using φ.app_smul r m

variable {X : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (φ : L.sheaf ⟶ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)

def lineBundleMorphismCoordinate (x : X) (W : X.Opens) (hW : W ≤ L.trivializingOpen x) : Γ(X, W) :=
  GlobalFrame.Cycles.structureModuleFrame X W (moduleSectionLinearMap φ W ((L.sectionFrame x W hW).symm 1))

theorem lineBundleMorphismCoordinate_apply (x : X) (W : X.Opens) (hW : W ≤ L.trivializingOpen x)
    (m : Γ(L.sheaf, W)) :
    GlobalFrame.Cycles.structureModuleFrame X W (moduleSectionLinearMap φ W m) =
      L.sectionFrame x W hW m * lineBundleMorphismCoordinate L φ x W hW := by
  let e := L.sectionFrame x W hW
  have hm : m = (e m) • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  change _ = e m * _
  conv_lhs => rw [hm]
  rw [map_smul, map_smul]
  rfl

theorem lineBundleMorphismCoordinate_restrict (x : X) {V W : X.Opens} (hVW : V ≤ W)
    (hW : W ≤ L.trivializingOpen x) :
    X.presheaf.map (homOfLE hVW).op (lineBundleMorphismCoordinate L φ x W hW) =
      lineBundleMorphismCoordinate L φ x V (hVW.trans hW) := by
  have hm : L.sheaf.presheaf.map (homOfLE hVW).op ((L.sectionFrame x W hW).symm 1) =
      (L.sectionFrame x V (hVW.trans hW)).symm 1 := by
    apply (L.sectionFrame x V (hVW.trans hW)).injective
    rw [L.sectionFrame_naturality x hVW hW, LinearEquiv.apply_symm_apply, map_one, LinearEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hVW).op)
    ((L.sectionFrame x W hW).symm 1)
  change X.presheaf.map (homOfLE hVW).op (φ.app W _) = φ.app V _
  exact hn.symm.trans (congrArg (φ.app V) hm)

theorem lineBundleMorphismCoordinate_transition (x y : X) (W : X.Opens)
    (hx : W ≤ L.trivializingOpen x) (hy : W ≤ L.trivializingOpen y) :
    lineBundleMorphismCoordinate L φ x W hx * (L.ambientTransitionOn x y W hx hy).val =
      lineBundleMorphismCoordinate L φ y W hy := by
  have h := lineBundleMorphismCoordinate_apply L φ x W hx ((L.sectionFrame y W hy).symm 1)
  exact (mul_comm _ _).trans h.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismCoordinate.Cycles
