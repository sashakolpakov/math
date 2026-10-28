import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Endomorphisms -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Endomorphisms.Core

noncomputable section

/-! Group-law preservation and finite actual morphism equations. The equation
language consists of natural families of morphism pairs, allowing all finite
identities formed using group operations, composition and fixed morphisms.
It is stronger than a chosen syntactic fragment and assumes no representing locus. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

/-- Equality with the identity and compatibility with multiplication on every
test scheme. Via Yoneda these are exactly the group-scheme morphism identities. -/
def PreservesGroupLaw {T : Over S} (f : T ⨯ A ⟶ A) : Prop :=
  ∀ (U : Over S) (t : U ⟶ T),
    prod.lift t (1 : U ⟶ A) ≫ f = 1 ∧
    ∀ x y : U ⟶ A,
      prod.lift t (x * y) ≫ f = (prod.lift t x ≫ f) * (prod.lift t y ≫ f)

theorem preservesGroupLaw_baseChange {T U : Over S} (a : T ⟶ U)
    (f : U ⨯ A ⟶ A) (hf : PreservesGroupLaw A f) :
    PreservesGroupLaw A (prod.map a (𝟙 A) ≫ f) := by
  intro V t
  have h := hf V (t ≫ a)
  simpa only [← Category.assoc, prod.lift_map, Category.comp_id] using h

def endomorphismSubfunctor : Subfunctor (HomFunctor.Hom.morphismFunctor A A) where
  obj _T := {f | PreservesGroupLaw A f}
  map a f hf := preservesGroupLaw_baseChange A a.unop f hf

def endomorphismTuples (n : ℕ) := Has.Core.tupleFunctor (endomorphismSubfunctor A).toFunctor n

def forgetGroupLaw (n : ℕ) : endomorphismTuples A n ⟶ Has.Core.morphismTuples A A n :=
  Has.Core.tupleNatTrans (endomorphismSubfunctor A).ι n

variable {A}

/-- A natural family of actual morphism identities. The source is flat,
proper and finitely presented; the target is separated. This includes group
identities and denominator-cleared identities involving a fixed polarization
or a natural duality operation, without assuming any equation locus. -/
structure FamilyMorphismEquation (F : (Over S)ᵒᵖ ⥤ Type u) where
  source : Over S
  target : Over S
  flat : Flat source.hom
  proper : IsProper source.hom
  finitelyPresented : LocallyOfFinitePresentation source.hom
  separated : IsSeparated target.hom
  lhs : F ⟶ HomFunctor.Hom.morphismFunctor source target
  rhs : F ⟶ HomFunctor.Hom.morphismFunctor source target

abbrev FiniteEndomorphismEquations (A : Over S) [GrpObj A] (n : ℕ) :=
  List (FamilyMorphismEquation (endomorphismTuples A n))

def SatisfiesEquations {F : (Over S)ᵒᵖ ⥤ Type u}
    (R : List (FamilyMorphismEquation F)) {T : (Over S)ᵒᵖ} (f : F.obj T) : Prop :=
  ∀ r ∈ R, r.lhs.app T f = r.rhs.app T f

def solutionSubfunctor {F : (Over S)ᵒᵖ ⥤ Type u}
    (R : List (FamilyMorphismEquation F)) : Subfunctor F where
  obj _ := {f | SatisfiesEquations R f}
  map a f hf := by
    intro r hr
    have hl := ConcreteCategory.congr_hom (r.lhs.naturality a) f
    have hh := ConcreteCategory.congr_hom (r.rhs.naturality a) f
    exact hl.trans ((congrArg ((HomFunctor.Hom.morphismFunctor r.source r.target).map a) (hf r hr)).trans hh.symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Endomorphisms.Core
