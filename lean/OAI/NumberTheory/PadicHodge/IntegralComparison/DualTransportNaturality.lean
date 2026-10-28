import OAI.NumberTheory.PadicHodge.IntegralComparison.DualHomologyTransport

/-! # Dual Transport Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DualTransportNaturality

noncomputable section

/-! Transporting a duality pairing along natural coefficient
isomorphisms preserves its naturality. -/

open _root_.CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R]

open OAI.NumberTheory.PadicHodge.IntegralComparison.DualHomologyTransport

def dualMap {M N : ModuleCat.{u} R} (a : M ⟶ N) : DualHomologyTransport.dualGroup R N ⟶ DualHomologyTransport.dualGroup R M :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat).map (ModuleCat.ofHom a.hom.dualMap)

@[reassoc]
theorem dualIso_naturality {M₁ M₂ D₁ D₂ : ModuleCat.{u} R}
    (a : M₁ ⟶ M₂) (b : D₁ ⟶ D₂) (e₁ : M₁ ≅ D₁) (e₂ : M₂ ≅ D₂)
    (h : a ≫ e₂.hom = e₁.hom ≫ b) :
    DualTransportNaturality.dualMap R a ≫ (DualHomologyTransport.dualIso R e₁).hom = (DualHomologyTransport.dualIso R e₂).hom ≫ DualTransportNaturality.dualMap R b := by
  have h' : e₁.inv ≫ a = b ≫ e₂.inv := by
    calc
      e₁.inv ≫ a = (e₁.inv ≫ (a ≫ e₂.hom)) ≫ e₂.inv := by simp [Category.assoc]
      _ = (e₁.inv ≫ (e₁.hom ≫ b)) ≫ e₂.inv := by rw [h]
      _ = b ≫ e₂.inv := by simp
  let F := ExactModuleDualFunctor.functor R ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat
  have hf := congrArg (fun f => F.map f.op) h'
  change F.map a.op ≫ F.map e₁.inv.op = F.map e₂.inv.op ≫ F.map b.op
  simpa only [op_comp, Functor.map_comp] using hf

@[reassoc]
theorem transport_naturality {A₁ A₂ : AddCommGrpCat.{u}}
    {M₁ M₂ D₁ D₂ : ModuleCat.{u} R}
    (u : A₂ ⟶ A₁) (a : M₁ ⟶ M₂) (b : D₁ ⟶ D₂)
    (p₁ : A₁ ≅ DualHomologyTransport.dualGroup R M₁) (p₂ : A₂ ≅ DualHomologyTransport.dualGroup R M₂)
    (e₁ : M₁ ≅ D₁) (e₂ : M₂ ≅ D₂)
    (hp : u ≫ p₁.hom = p₂.hom ≫ DualTransportNaturality.dualMap R a)
    (he : a ≫ e₂.hom = e₁.hom ≫ b) :
    u ≫ (DualHomologyTransport.transport R p₁ e₁).hom = (DualHomologyTransport.transport R p₂ e₂).hom ≫ DualTransportNaturality.dualMap R b := by
  exact DualComplexHomology.compose_squares _ _ _ _ _ _ _ hp
    (dualIso_naturality R a b e₁ e₂ he)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DualTransportNaturality
