import OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Geometric Points -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricPoints.Construction

/-! Geometric points and their characteristic, derived from the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure GeometricPoint (S : Scheme.{u}) where
  field : Type u
  fieldStructure : Field field
  algebraicallyClosed : IsAlgClosed field
  map : Spec (.of field) ⟶ S

attribute [instance] GeometricPoint.fieldStructure GeometricPoint.algebraicallyClosed

theorem charP_of_geometric_map (p : ℕ) (hp : p.Prime) {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (k : Type u) [Field k] (s : Spec (.of k) ⟶ S) :
    CharP k p := by
  apply (CharP.charP_iff_prime_eq_zero hp).mpr
  have h := Frobenius.Construction.prime_eq_zero_of_map p hS s
  have hk := congrArg (Scheme.ΓSpecIso (.of k)).hom h
  simpa only [map_natCast, map_zero] using hk

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricPoints.Construction
