import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicSheafResolution

/-! # Acyclic Resolution Dimension Shift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionDimensionShift.IntrinsicCech

noncomputable section

/-! Actual connecting maps identify the positive cohomology of the cycle sheaves in an acyclic resolution with shifted cohomology of the resolved sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}}

def acyclicMiddleCohomologyShift
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n))
    (h₁ : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (n + 1))) :
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n :
      _ ⥤ AddCommGrpCat.{u}).obj S.X₃) ≃+
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1) :
      _ ⥤ AddCommGrpCat.{u}).obj S.X₁) := by
  letI : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n) := h₀
  letI : Subsingleton (CategoryTheory.Sheaf.H S.X₂ (n + 1)) := h₁
  let d := HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.δ hS n (n + 1) rfl
  apply AddEquiv.ofBijective d
  constructor
  · intro x y hxy
    have hzero : d (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₃_explicit hS n (n + 1) rfl (x - y) hzero
    have hz0 : z = 0 := Subsingleton.elim _ _
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  · intro y
    exact HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₁_explicit hS n (n + 1) rfl y (Subsingleton.elim _ _)

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ⟶ K.X 0)
    (w : e ≫ K.d 0 1 = 0) [he : Mono e]
    (haug : (ShortComplex.mk e (K.d 0 1) w).Exact)
    (hpos : ∀ n, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).Exact)
    (hK : ∀ p q, Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)))

include he in
def resolutionCycleCohomologyShift (n q : ℕ) :
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (q + 1) :
      _ ⥤ AddCommGrpCat.{u}).obj (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K n).cycles) ≃+
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + q + 2) :
      _ ⥤ AddCommGrpCat.{u}).obj F) := by
  induction n generalizing q with
  | zero =>
      have hq : 0 + q + 2 = (q + 1) + 1 := by omega
      rw [hq]
      exact acyclicMiddleCohomologyShift
        (@AcyclicSheafResolution.IntrinsicCech.initialResolutionCycleSequence_shortExact X K F e w he haug hpos) (q + 1)
        (hK 0 q) (hK 0 (q + 1))
  | succ n ih =>
      let d := acyclicMiddleCohomologyShift
        (AcyclicSheafResolution.IntrinsicCech.successiveResolutionCycleSequence_shortExact K hpos n) (q + 1)
        (hK (n + 1) q) (hK (n + 1) (q + 1))
      have hn : n + (q + 1) + 2 = (n + 1) + q + 2 := by omega
      rw [← hn]
      exact d.trans (ih (q + 1))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionDimensionShift.IntrinsicCech
