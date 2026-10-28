import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese

/-! # Albanese -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Albanese

noncomputable section

/-!
TateComparison's componentwise Albanese input uses IntegralModel's actual pointed universal
property. Candidate maps contain no universal-property or Hecke-action field.
Their existence and universality are constructed from the explicit Construction input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- The chosen, pointed, smooth projective complex components. -/
structure PointedComponents (r : ℕ) where
  variety : Fin r → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety
  basePoint : ∀ j, Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ (variety j).toOver

/-- Candidate Albanese varieties and maps; universality is a separate predicate. -/
structure ComponentAlbaneseCandidates {r : ℕ} (X : PointedComponents r) where
  abelian : Fin r → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  map : ∀ j, (X.variety j).toOver ⟶ (abelian j).toOver

namespace ComponentAlbaneseCandidates

variable {r : ℕ} {X : PointedComponents r}

/-- Exactly the componentwise Albanese property used in the IntegralModel input. -/
def IsAlbanese (D : ComponentAlbaneseCandidates X) : Prop :=
  ∀ j, PELModuli.IntegralModel.Albanese.IsAlbaneseMap (X.variety j).presentation
    (X.basePoint j) (D.abelian j) (D.map j)

/-- Actual candidates are chosen from the explicitly supplied Construction proposition. -/
def ofConstruction (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (X : PointedComponents r) :
    ComponentAlbaneseCandidates X where
  abelian j := (hConstruction (X.variety j).presentation (X.basePoint j)).choose
  map j := (hConstruction (X.variety j).presentation (X.basePoint j)).choose_spec.choose

theorem ofConstruction_isAlbanese (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (X : PointedComponents r) :
    (ofConstruction hConstruction X).IsAlbanese := by
  intro j
  exact (hConstruction (X.variety j).presentation (X.basePoint j)).choose_spec.choose_spec

end ComponentAlbaneseCandidates

/-- The structural map as a map to the terminal object over the complex base. -/
def componentToBase (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    X.toOver ⟶ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) :=
  Over.homMk X.structureMap (by simp)

theorem point_componentToBase (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) : x ≫ componentToBase X = 𝟙 _ := by
  ext
  exact x.w

/-- Subtracting the value at the base point is an actual algebraic map. -/
def normalizeAlbaneseMorphism (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) : X.toOver ⟶ A.toOver :=
  f / (componentToBase X ≫ x₀ ≫ f)

theorem normalizeAlbaneseMorphism_point (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver) :
    x₀ ≫ normalizeAlbaneseMorphism X x₀ A f = 1 := by
  simp [normalizeAlbaneseMorphism, GrpObj.comp_div, ← Category.assoc,
    point_componentToBase]

/-- Universality produces an integral algebraic endomorphism for an actual
algebraic trace map, once that map has been constructed. No trace existence
or compatibility is included in the hypotheses. -/
theorem albanese_endomorphism_of_morphism
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
    (ha : PELModuli.IntegralModel.Albanese.IsAlbaneseMap X.presentation x₀ A a)
    (f : X.toOver ⟶ A.toOver) :
    ∃! e : End.IntegralEnd A.toOver,
      a ≫ End.endSchemeMap A.toOver e = normalizeAlbaneseMorphism X x₀ A f := by
  obtain ⟨φ, hφ, huniq⟩ := ha.2 A (normalizeAlbaneseMorphism X x₀ A f)
    (normalizeAlbaneseMorphism_point X x₀ A f)
  let : IsMonHom φ := hφ.1
  refine ⟨End.endOfSchemeMap A.toOver φ, ?_, ?_⟩
  · simpa using hφ.2
  · intro e he
    apply End.endSchemeMap_injective A.toOver
    rw [End.endSchemeMap_ofSchemeMap]
    exact huniq (End.endSchemeMap A.toOver e) ⟨inferInstance, he⟩

/-- The induced homomorphism acts by point push on differences within a
component. The group-object notation writes the additive difference as `/`. -/
theorem albanese_endomorphism_point_differences
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a f : X.toOver ⟶ A.toOver)
    (e : End.IntegralEnd A.toOver)
    (he : a ≫ End.endSchemeMap A.toOver e = normalizeAlbaneseMorphism X x₀ A f)
    (x y : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ((x ≫ a) / (y ≫ a)) ≫ End.endSchemeMap A.toOver e = (x ≫ f) / (y ≫ f) := by
  rw [GrpObj.div_comp, Category.assoc, Category.assoc, he]
  simp [normalizeAlbaneseMorphism, GrpObj.comp_div, ← Category.assoc,
    point_componentToBase]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Albanese
