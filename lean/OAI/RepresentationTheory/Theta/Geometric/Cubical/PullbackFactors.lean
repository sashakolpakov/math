import OAI.RepresentationTheory.Theta.Geometric.AutomorphyFactorOperations
import OAI.RepresentationTheory.Theta.Geometric.Cubical.Automorphy
import OAI.RepresentationTheory.Theta.Geometric.Period.PolarizationBundle

/-! # Pullback Factors -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The two cubical products use exactly the same automorphy factor
after any three linear period maps. -/

section

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData}

theorem Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem (f g : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice)
    (hg : ∀ l : Ψ.periodIntegerLattice, g l.val ∈ Φ.periodIntegerLattice)
    (l : Ψ.periodIntegerLattice) : (f + g) l.val ∈ Φ.periodIntegerLattice :=
  Φ.periodIntegerLattice.add_mem (hf l) (hg l)

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.ext_value (J K : Φ.AutomorphyFactor) (h : ∀ l z, J.value l z = K.value l z) : J = K := by
  cases J with
  | mk j j0 ja jc =>
    cases K with
    | mk k k0 ka kc =>
      have hj : j = k := funext (fun l => funext (h l))
      cases hj
      rfl

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.IsCubical (J : Φ.AutomorphyFactor) : Prop :=
  ∀ (l m n : Φ.periodIntegerLattice) (w z u : Φ.space),
    J.value (l + m + n) (w + z + u) * J.value l w * J.value m z * J.value n u =
      J.value (l + m) (w + z) * J.value (l + n) (w + u) * J.value (m + n) (z + u)

variable (J : Φ.AutomorphyFactor) (f g h : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice)
    (hg : ∀ l : Ψ.periodIntegerLattice, g l.val ∈ Φ.periodIntegerLattice)
    (hh : ∀ l : Ψ.periodIntegerLattice, h l.val ∈ Φ.periodIntegerLattice)

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.leftCubeFactor : Ψ.AutomorphyFactor :=
  (((J.comap (f + g + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem (f + g) h (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg) hh)).mul
    (J.comap f hf)).mul (J.comap g hg)).mul (J.comap h hh)

def Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.rightCubeFactor : Ψ.AutomorphyFactor :=
  ((J.comap (f + g) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg)).mul
    (J.comap (f + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f h hf hh))).mul
      (J.comap (g + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem g h hg hh))

theorem Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.cubeFactors_eq (hJ : J.IsCubical) :
    J.leftCubeFactor f g h hf hg hh = J.rightCubeFactor f g h hf hg hh := by
  apply Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.ext_value
  intro l z
  exact hJ (Torus.Data.CM.ProjectivePeriodData.latticeMapOfLinear f hf l) (Torus.Data.CM.ProjectivePeriodData.latticeMapOfLinear g hg l) (Torus.Data.CM.ProjectivePeriodData.latticeMapOfLinear h hh l)
    (f z) (g z) (h z)

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodPolarizationFactor_isCubical (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    (D.periodPolarizationFactor hg x).IsCubical := by
  intro l m n w z u
  have H := D.periodPolarizationAutomorphy_cube hg x ((D.periodLatticeEquiv hg x).symm l)
    ((D.periodLatticeEquiv hg x).symm m) ((D.periodLatticeEquiv hg x).symm n) w z u
  simp only [Data.ActiveHeckeThetaData.periodPolarizationFactor, map_add]
  exact H

end

end OAI.RepresentationTheory.Theta.Geometric
