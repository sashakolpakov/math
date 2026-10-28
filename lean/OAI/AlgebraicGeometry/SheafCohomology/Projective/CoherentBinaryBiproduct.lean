import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTypeIso

/-! # Coherent Binary Biproduct -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentBinaryBiproduct

noncomputable section

/-! Binary biproducts of actual coherent module sheaves are coherent. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def finTwoCoproductIsoBiprod {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteCoproducts C] [HasBinaryBiproducts C] (M N : C) :
    (∐ ![M, N]) ≅ M ⊞ N where
  hom := Sigma.desc (Fin.cases biprod.inl (Fin.cases biprod.inr (fun i => Fin.elim0 i)))
  inv := biprod.desc (Sigma.ι ![M, N] 0) (Sigma.ι ![M, N] 1)
  hom_inv_id := by
    ext i
    fin_cases i <;> simp
    change (biprod.inr : N ⟶ M ⊞ N) ≫ _ = _
    simp
  inv_hom_id := by
    ext <;> simp
    all_goals change (biprod.inr : N ⟶ M ⊞ N) ≫ _ = _
    all_goals simp

theorem module_biprod_quasicoherent {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent := by
  have hq : (∐ ![M, N]).IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _
    (fun i => by fin_cases i <;> dsimp <;> infer_instance)
  exact (Quasicoherent.Scheme.Modules.isQuasicoherent X).prop_of_iso (finTwoCoproductIsoBiprod M N) hq

theorem module_biprod_finiteType {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType] :
    (M ⊞ N).IsFiniteType := by
  have : (∐ ![M, N]).IsFiniteType := Quasicoherent.Scheme.Modules.isFiniteType_fin_coproduct _
    (fun i => by fin_cases i <;> dsimp <;> infer_instance)
    (fun i => by fin_cases i <;> dsimp <;> infer_instance)
  exact FiniteTypeIso.finiteType_of_iso (finTwoCoproductIsoBiprod M N)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentBinaryBiproduct
