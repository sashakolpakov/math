import OAI.RepresentationTheory.Theta.Geometric.ProductPeriodData

/-! # Triple Period Maps -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The three coordinate maps of the literal triple period lattice. -/

variable (Φ : Torus.Data.CM.ProjectivePeriodData)

def Torus.Data.CM.ProjectivePeriodData.triple : Torus.Data.CM.ProjectivePeriodData := (Φ.product Φ).product Φ

def Torus.Data.CM.ProjectivePeriodData.tripleFirst : Φ.triple.space →L[ℂ] Φ.space :=
  (ContinuousLinearMap.fst ℂ Φ.space Φ.space).comp
    (ContinuousLinearMap.fst ℂ (Φ.space × Φ.space) Φ.space)

def Torus.Data.CM.ProjectivePeriodData.tripleSecond : Φ.triple.space →L[ℂ] Φ.space :=
  (ContinuousLinearMap.snd ℂ Φ.space Φ.space).comp
    (ContinuousLinearMap.fst ℂ (Φ.space × Φ.space) Φ.space)

def Torus.Data.CM.ProjectivePeriodData.tripleThird : Φ.triple.space →L[ℂ] Φ.space :=
  ContinuousLinearMap.snd ℂ (Φ.space × Φ.space) Φ.space

theorem Torus.Data.CM.ProjectivePeriodData.tripleFirst_mem (l : Φ.triple.periodIntegerLattice) :
    Φ.tripleFirst l.val ∈ Φ.periodIntegerLattice := l.property.1.1

theorem Torus.Data.CM.ProjectivePeriodData.tripleSecond_mem (l : Φ.triple.periodIntegerLattice) :
    Φ.tripleSecond l.val ∈ Φ.periodIntegerLattice := l.property.1.2

theorem Torus.Data.CM.ProjectivePeriodData.tripleThird_mem (l : Φ.triple.periodIntegerLattice) :
    Φ.tripleThird l.val ∈ Φ.periodIntegerLattice := l.property.2

theorem Torus.Data.CM.ProjectivePeriodData.triple_coordinate_nonzero (v : Φ.triple.space) (hv : v ≠ 0) :
    Φ.tripleFirst v ≠ 0 ∨ Φ.tripleSecond v ≠ 0 ∨ Φ.tripleThird v ≠ 0 := by
  by_cases h1 : Φ.tripleFirst v = 0
  · by_cases h2 : Φ.tripleSecond v = 0
    · exact Or.inr (Or.inr (fun h3 => hv (Prod.ext (Prod.ext h1 h2) h3)))
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

theorem Torus.Data.CM.ProjectivePeriodData.triple_coordinate_outside (p q : Φ.triple.space)
    (hpq : p - q ∉ Φ.triple.periodIntegerLattice) :
    Φ.tripleFirst p - Φ.tripleFirst q ∉ Φ.periodIntegerLattice ∨
      Φ.tripleSecond p - Φ.tripleSecond q ∉ Φ.periodIntegerLattice ∨
      Φ.tripleThird p - Φ.tripleThird q ∉ Φ.periodIntegerLattice := by
  by_cases h1 : Φ.tripleFirst p - Φ.tripleFirst q ∈ Φ.periodIntegerLattice
  · by_cases h2 : Φ.tripleSecond p - Φ.tripleSecond q ∈ Φ.periodIntegerLattice
    · exact Or.inr (Or.inr (fun h3 => hpq ⟨⟨h1, h2⟩, h3⟩))
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

end

end OAI.RepresentationTheory.Theta.Geometric
