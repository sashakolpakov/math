import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsHas

/-! # Component Finite Diagram -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentFiniteDiagram

noncomputable section

/-! Encode all component sources, abelian targets, base points and maps
in the actual finite diagram accepted by the proved SpreadingOut construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

abbrev ComponentDiagramIndex (r : ℕ) := Option (Fin r ⊕ Fin r)

def componentDiagramObject
    {R : Type} [Field R] [NumberField R] {T : Over (Spec (.of R))} {r : ℕ}
    (D : Components.ComponentAlbaneseData T r) : ComponentDiagramIndex r → Over (Spec (.of R))
  | none => 𝟙_ (Over (Spec (.of R)))
  | some (.inl i) => D.S i
  | some (.inr i) => (D.A i).X

def componentFiniteDiagram
    {R : Type} [Field R] [NumberField R] {T : Over (Spec (.of R))} {r : ℕ}
    (D : Components.ComponentAlbaneseData T r)
    (hS : ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom)
    (hA : ∀ i, Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧ GeometricallyConnected (D.A i).X.hom) :
    ModelsHas.FiniteDiagram R where
  objects := ComponentDiagramIndex r
  arrows := Fin r ⊕ Fin r
  abelians := Fin r
  X := componentDiagramObject D
  smooth
    | none => inferInstanceAs (Smooth (𝟙 _))
    | some (.inl i) => (hS i).1
    | some (.inr i) => (hA i).1
  proper
    | none => inferInstanceAs (IsProper (𝟙 _))
    | some (.inl i) => (hS i).2
    | some (.inr i) => (hA i).2.1
  src
    | .inl _ => none
    | .inr i => some (.inl i)
  dst
    | .inl i => some (.inl i)
    | .inr i => some (.inr i)
  f
    | .inl i => D.x₀ i
    | .inr i => D.a i
  abelianIndex i := some (.inr i)
  group i := (D.A i).grp
  abelian i := ⟨(D.A i).comm, (hA i).2.2⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentFiniteDiagram
