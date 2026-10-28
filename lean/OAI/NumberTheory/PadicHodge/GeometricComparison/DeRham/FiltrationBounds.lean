import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE

/-! # Filtration Bounds -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationBounds

noncomputable section

/-! Bounds on the native filtration, proved from the actual truncated complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable (R : Type*) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

theorem filtration_eq_top (n : ℕ) (r : ℤ) (hr : r ≤ 0) :
    AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r = ⊤ := by
  let : IsIso (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r) :=
    TruncationBoundsGE.TruncationBounds.isIso_inclusion_of_nonpositive _ r hr
  apply LinearMap.range_eq_top.mpr
  exact TruncationBoundsGE.TruncationBounds.rightComp_surjective
    ((shiftFunctor (DerivedCategory (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.Sheaves R X)) (n : ℤ)).map
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.derivedFunctor R X).map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)))

theorem filtration_eq_bot (n : ℕ) (r : ℤ) (hr : (n : ℤ) < r) :
    AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r = ⊥ := by
  let D := (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.derivedFunctor R X).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)
  let : CochainComplex.IsStrictlyGE
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r).extend ComplexShape.embeddingUpNat) r :=
    TruncationBoundsGE.TruncationBounds.extended_isStrictlyGE _ r
  let : D.IsGE r := by
    change (DerivedCategory.Q.obj
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r).extend ComplexShape.embeddingUpNat)).IsGE r
    infer_instance
  let : (D⟦(n : ℤ)⟧).IsGE (r - (n : ℤ)) :=
    DerivedCategory.TStructure.t.isGE_shift D r (n : ℤ) (r - (n : ℤ)) (by omega)
  apply le_antisymm _ bot_le
  rintro _ ⟨x, rfl⟩
  have hx : x = 0 := DerivedCategory.TStructure.t.zero x 0 (r - (n : ℤ)) (by omega)
  rw [hx, map_zero]
  exact Submodule.zero_mem _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationBounds
