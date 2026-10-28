import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.BinaryBiproduct

/-! # Zero Module Coherence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroModuleCoherence

noncomputable section

/-! Zero scheme modules are quasicoherent and finite type. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem module_coherent_of_isZero {X : Scheme.{u}} (M : X.Modules) (hM : IsZero M) :
    M.IsQuasicoherent ∧ M.IsFiniteType := by
  let Q : ULift.{u} Empty → X.Modules := fun i => nomatch i.down
  have hq : (∐ Q).IsQuasicoherent :=
    Quasicoherent.Coproducts.module_quasicoherent_coproduct Q (fun i => nomatch i.down)
  have : (∐ Q).IsFiniteType :=
    Quasicoherent.FiniteCoproducts.module_finiteType_finite_coproduct Q
      (fun i => nomatch i.down) (fun i => nomatch i.down)
  have hz : IsZero (∐ Q) := (IsZero.iff_id_eq_zero _).mpr (by
    apply Sigma.hom_ext
    intro i
    exact i.down.elim)
  let e : (∐ Q) ≅ M := hz.iso hM
  have hm : M.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq
  exact ⟨hm, Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroModuleCoherence
