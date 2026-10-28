import OAI.Analysis.PDE.Schauder.Calculus.TransformedBackground
import OAI.Analysis.PDE.Schauder.Calculus.HolderPeriodicity

open Set Module
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {X : Type*} [MetricSpace X] {α : ℝ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance transformedValueDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance transformedValueDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance transformedValueEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance transformedValueEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance transformedValueSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance transformedValueSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance transformedValueMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance transformedValueMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def transformedJetMoore
    (B₀ : E →L[ℝ] E →L[ℝ] ℝ) (J : E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E)
    (p : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    B₀ (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j) +
      (B (J (OAI.Analysis.PDE.Dirichlet.coordinateVector i)) (J (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) +
        p (T (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)))))

theorem value_transformedBackgroundMooreField (hα : 0 ≤ α)
    (B₀ : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedBackgroundMooreField hα B₀ J T p B) x =
      transformedJetMoore (OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀ x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value T x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value p x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x) := by
  rw [transformedBackgroundMooreField,OAI.Analysis.Normed.Function.Holder.value_mooreDetField]
  rfl

theorem transformedBackgroundMooreField_periodic
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {r : E → ℝ} (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hα : 0 ≤ α)
    (B₀ : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (hB₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀)))
    (hJ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value J)))
    (hT : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value T)))
    (hp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value p)))
    (hB : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value B))) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedBackgroundMooreField hα B₀ J T p B))) := by
  apply holder_periodic_of_value_eq e b hr
  intro x y l hy
  rw [value_transformedBackgroundMooreField,value_transformedBackgroundMooreField,
    holder_value_eq_of_periodic e b B₀ hB₀ x y l hy,
    holder_value_eq_of_periodic e b J hJ x y l hy,
    holder_value_eq_of_periodic e b T hT x y l hy,
    holder_value_eq_of_periodic e b p hp x y l hy,
    holder_value_eq_of_periodic e b B hB x y l hy]

end OAI.Analysis.PDE.Schauder
