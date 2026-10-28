import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.ModelGlobalFunctions
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.FiniteCechModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalPointedCechCover
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ResidueCechConstants

/-! # Local Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.LocalGlobalFunctions.Construction

noncomputable section

/-! Every global function on a proper smooth family with connected
geometric fibers and a section comes from its Noetherian local base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false in
theorem noetherianLocal_globalFunctions_isIso
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) : IsIso f.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨I, hIfin, hIorder, U, hUa, hU, a, ha⟩ := LocalPointedCechCover.Construction.exists_local_pointed_finite_cech_cover σ
  let := hIfin
  let := hIorder
  obtain ⟨D, φ, hφ, hf, hp, ht⟩ := Relative.FiniteCechModel.Construction.relativeStructureCech_exists_finite_projective_model f U hU hUa
  have := hφ
  have := hf 0
  have := hf 1
  have := hp 1
  have : Module.Free R (D.X 1) := Module.free_of_flat_of_isLocalRing
  have := ht (IsLocalRing.ResidueField R)
  exact Finite.ModelGlobalFunctions.Construction.globalFunctions_iso_of_finite_cech_model f σ hσ U hU a ha φ
    (ResidueCechConstants.Construction.residueCech_constants_exact f σ hσ U hU hUa)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.LocalGlobalFunctions.Construction
