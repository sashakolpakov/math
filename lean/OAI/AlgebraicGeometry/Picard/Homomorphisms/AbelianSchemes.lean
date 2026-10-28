import OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricPoints
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Abelian Schemes -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.AbelianSchemes.Construction

/-! The geometric abelian-scheme bundle used by Homomorphisms, allowing its
relative dimension to vary on the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

structure AbelianScheme (S : Scheme.{u}) where
  toOver : Over S
  [group : GrpObj toOver]
  [commutative : IsCommMonObj toOver]
  [proper : IsProper toOver.hom]
  [smooth : Smooth toOver.hom]
  [connected : GeometricallyConnected toOver.hom]

attribute [instance] AbelianScheme.group AbelianScheme.commutative
  AbelianScheme.proper AbelianScheme.smooth AbelianScheme.connected

noncomputable def AbelianScheme.pullback {S T : Scheme.{u}}
    (A : AbelianScheme S) (f : T ⟶ S) : AbelianScheme T where
  toOver := (Over.pullback f).obj A.toOver
  group := Functor.grpObjObj
  commutative := inferInstance
  proper := inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd A.toOver.hom f))
  smooth := inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd A.toOver.hom f))
  connected := inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd A.toOver.hom f))

noncomputable def AbelianScheme.geometricFiber {S : Scheme.{u}}
    (A : AbelianScheme S) (s : GeometricPoints.Construction.GeometricPoint S) : AbelianScheme (Spec (.of s.field)) :=
  A.pullback s.map

end OAI.AlgebraicGeometry.Picard.Homomorphisms.AbelianSchemes.Construction
