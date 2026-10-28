import OAI.Geometry.ComplexBall.IntegralLattice

/-! # Stable CM Real Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric.StableCMRealLattice

noncomputable section

/-! The original full CM-stable lattice is a full lattice over the
maximal real subfield in the actual six-dimensional coordinates. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (L : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hL : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice L)

def stableRealModule : Submodule (𝓞 (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E)) (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) where
  carrier := L
  zero_mem' := L.zero_mem
  add_mem' := L.add_mem
  smul_mem' a x hx := hL.2.2
    ⟨algebraMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) E a, map_isIntegral_int (algebraMap (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) E) a.property⟩ x hx

omit [IsCMField E] in
theorem stableRealModule_finite : (stableRealModule L hL).FG := by
  apply Submodule.FG.of_restrictScalars ℤ
  exact hL.1

omit [IsCMField E] in
theorem stableRealModule_full :
    Submodule.span (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (stableRealModule L hL : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ := by
  have hle : Submodule.span ℚ (L : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) ≤
      (Submodule.span (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (stableRealModule L hL : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))).restrictScalars ℚ :=
    Submodule.span_le.mpr (fun _ hx => Submodule.subset_span hx)
  rw [hL.2.1] at hle
  exact top_unique hle

variable (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

def stableRealCoordinateModule : Submodule (𝓞 (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E)) (Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) :=
  (stableRealModule L hL).map ((Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).toLinearMap.restrictScalars (𝓞 (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E)))

theorem stableRealCoordinateModule_full :
    Submodule.span (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) (stableRealCoordinateModule L hL δ hδ hδ0 : Set (Fin 6 → Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E)) = ⊤ := by
  change Submodule.span (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E)
    ((Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).toLinearMap '' (stableRealModule L hL : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))) = ⊤
  rw [← Submodule.map_span, stableRealModule_full, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).surjective

def stableRealLattice : NumberTheory.ArithmeticGroups.Lattices.IntegralLattice.FullLattice (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RealField E) 6 where
  module := stableRealCoordinateModule L hL δ hδ hδ0
  finite := (stableRealModule_finite L hL).map _
  full := stableRealCoordinateModule_full L hL δ hδ hδ0

theorem stableRealLattice_mem (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0 x ∈ (stableRealLattice L hL δ hδ hδ0).module ↔ x ∈ L := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Geometry.ComplexBall.IntegralLattice.ArithmeticQuotient.cmCoordinates δ hδ hδ0).injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end

end OAI.RepresentationTheory.Theta.Geometric.StableCMRealLattice
