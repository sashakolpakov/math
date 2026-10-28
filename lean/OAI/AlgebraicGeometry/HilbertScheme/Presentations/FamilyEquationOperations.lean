import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Endomorphisms
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Family Equation Operations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! Reindex natural morphism equations along natural transformations,
preserving their actual source and target geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}

def Endomorphisms.Core.FamilyMorphismEquation.comap (r : Endomorphisms.Core.FamilyMorphismEquation G) (φ : F ⟶ G) :
    Endomorphisms.Core.FamilyMorphismEquation F where
  source := r.source
  target := r.target
  flat := r.flat
  proper := r.proper
  finitelyPresented := r.finitelyPresented
  separated := r.separated
  lhs := φ ≫ r.lhs
  rhs := φ ≫ r.rhs

theorem FamilyEquationOperations.Core.satisfiesEquations_comap (R : List (Endomorphisms.Core.FamilyMorphismEquation G)) (φ : F ⟶ G)
    {T : (Over S)ᵒᵖ} (f : F.obj T) :
    Endomorphisms.Core.SatisfiesEquations (R.map (fun r => r.comap φ)) f ↔ Endomorphisms.Core.SatisfiesEquations R (φ.app T f) := by
  constructor
  · intro h r hr
    exact h (r.comap φ) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  · intro h r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    exact h r' hr'

def FamilyEquationOperations.Core.tupleProjection (F : (Over S)ᵒᵖ ⥤ Type u) (n : ℕ) (i : Fin n) : Has.Core.tupleFunctor F n ⟶ F where
  app _T := ↾fun f => f i
  naturality _T _U _a := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
