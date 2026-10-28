import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

/-! # Field Frobenius Geometry -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FieldFrobeniusGeometry.FiniteFieldFrobeniusGeometry

noncomputable section

/-! Identify the actual finite-field Frobenius conventions on schemes before comparing their cohomological realizations. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

variable (p a : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (hcard : Fintype.card k = p ^ a)

theorem scalarFrobenius_eq (κ : k →+* Γ(Spec (CommRingCat.of (AlgebraicClosure k)), ⊤)) :
    AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k (Spec (CommRingCat.of (AlgebraicClosure k))) κ =
      (IntegralComparison.Frobenius.Geometry.scalarSchemeIso (IntegralComparison.Frobenius.Geometry.arithmeticFrobenius p a k hcard)).hom := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv ≫
      (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.qPowerSchemeFrobenius k (Spec (CommRingCat.of (AlgebraicClosure k))) κ).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv ≫
      (Spec.map (CommRingCat.ofHom (IntegralComparison.Frobenius.Geometry.arithmeticFrobenius p a k hcard).toRingHom)).appTop
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext x
  change ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv x) ^ Fintype.card k =
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv (IntegralComparison.Frobenius.Geometry.arithmeticFrobenius p a k hcard x)
  rw [IntegralComparison.Frobenius.Geometry.arithmeticFrobenius_apply, hcard]
  exact (map_pow (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv.hom x (p ^ a)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FieldFrobeniusGeometry.FiniteFieldFrobeniusGeometry
