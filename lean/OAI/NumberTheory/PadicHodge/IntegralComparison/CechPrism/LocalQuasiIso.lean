import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartModuleCechTotal

/-! # Local Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalQuasiIso

noncomputable section

/-! The actual local diagonal augmentation is a quasi-isomorphism
whenever its own-chart coefficient map is; the remaining hypotheses
are only the genuine inverse-meet restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable {C : Type v} [SemilatticeInf C]
  (R : Type u) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u w} R) ℕ)
  (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex (ModuleCat.{max u w} R) ℕ)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))
  (I : C) (i : ι) (hi : I ≤ U i)

omit [Finite ι] in
theorem self : (LocalAugmentation.cone Q B γ h (op I)).app (op I) =
    (γ.app (op I)).app (op I) := by
  change (γ.app (op I)).app (op I) ≫
    (GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.cone C I (B.obj (op I)) (fun V => h V I)).app (op I) = _
  rw [GeometricComparison.Semilattice.LocalCone.SemilatticeLocalCone.self, Category.comp_id]

include hi in
omit [Finite ι] in
theorem quasiIso [QuasiIso ((γ.app (op I)).app (op I))] :
    QuasiIso ((LocalAugmentation.map U Q B γ h).app (op I)) := by
  have : QuasiIso ((LocalAugmentation.cone Q B γ h (op I)).app (op I)) :=
    (self R Q B γ h I).symm ▸ inferInstance
  exact GeometricComparison.Semilattice.SubchartModuleCechTotal.SemilatticeSubchartModuleCechTotal.quasiIso R C U I i hi
    (B.obj (op I)) (fun V => h V I) (Q.obj (op I))
    (LocalAugmentation.cone Q B γ h (op I))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalQuasiIso
