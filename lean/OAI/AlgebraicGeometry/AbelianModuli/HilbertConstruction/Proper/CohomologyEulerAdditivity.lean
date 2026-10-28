import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.CohomologyEulerAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CohomologyBound

/-! # Cohomology Euler Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerAdditivity

noncomputable section

/-! Genuine coherent Euler characteristic is additive on short exact sequences over a proper scheme over a field. Finiteness and cohomology bounds are proved from the geometry. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem proper_coherent_euler_additive
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₁.IsFiniteType]
    [S.X₂.IsQuasicoherent] [S.X₂.IsFiniteType]
    [S.X₃.IsQuasicoherent] [S.X₃.IsFiniteType] :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p S.X₂ =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p S.X₁ + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p S.X₃ := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨N₁, h₁⟩ := Quasicoherent.CohomologyBound.compactSeparated_quasicoherent_cohomology_bounded (Coefficient.ModulePresheaf.schemeCoefficientMap p) S.X₁
  obtain ⟨N₂, h₂⟩ := Quasicoherent.CohomologyBound.compactSeparated_quasicoherent_cohomology_bounded (Coefficient.ModulePresheaf.schemeCoefficientMap p) S.X₂
  obtain ⟨N₃, h₃⟩ := Quasicoherent.CohomologyBound.compactSeparated_quasicoherent_cohomology_bounded (Coefficient.ModulePresheaf.schemeCoefficientMap p) S.X₃
  exact Bounded.CohomologyEulerAdditivity.coefficientEulerCharacteristic_shortExact_of_bounded p hS
    (CoherentCohomology.proper_coherent_cohomologyFinite p S.X₁)
    (CoherentCohomology.proper_coherent_cohomologyFinite p S.X₂)
    (CoherentCohomology.proper_coherent_cohomologyFinite p S.X₃)
    (max N₁ (max N₂ N₃))
    (fun q hq => h₁ q (by omega)) (fun q hq => h₂ q (by omega)) (fun q hq => h₃ q (by omega))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerAdditivity
