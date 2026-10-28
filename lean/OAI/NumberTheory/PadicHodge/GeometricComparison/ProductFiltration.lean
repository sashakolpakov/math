import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationTransportT

/-! # Product Filtration -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProductFiltration.FiltrationTransport

noncomputable section

/-! Product filtrations have the sum of the actual Hodge numbers. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def product (F : Linear.FiniteFiltration K V) (G : Linear.FiniteFiltration K W) : Linear.FiniteFiltration K (V × W) where
  step i := (F.step i).prod (G.step i)
  antitone_step _ _ hij := Submodule.prod_mono (F.antitone_step hij) (G.antitone_step hij)
  eventually_top := by
    obtain ⟨a, ha⟩ := F.eventually_top
    obtain ⟨b, hb⟩ := G.eventually_top
    refine ⟨min a b, ?_⟩
    rw [F.step_eq_top ha (min_le_left _ _), G.step_eq_top hb (min_le_right _ _), Submodule.prod_top]
  eventually_bot := by
    obtain ⟨a, ha⟩ := F.eventually_bot
    obtain ⟨b, hb⟩ := G.eventually_bot
    refine ⟨max a b, ?_⟩
    rw [F.step_eq_bot ha (le_max_left _ _), G.step_eq_bot hb (le_max_right _ _), Submodule.prod_bot]

def productSubmoduleEquiv (P : Submodule K V) (Q : Submodule K W) : (P × Q) ≃ₗ[K] P.prod Q where
  toFun x := ⟨(x.1, x.2), x.1.property, x.2.property⟩
  invFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [FiniteDimensional K V] [FiniteDimensional K W]

theorem product_step_finrank (F : Linear.FiniteFiltration K V) (G : Linear.FiniteFiltration K W) (i : ℤ) :
    Module.finrank K ((product F G).step i) = Module.finrank K (F.step i) + Module.finrank K (G.step i) :=
  (productSubmoduleEquiv (F.step i) (G.step i)).finrank_eq.symm.trans Module.finrank_prod

theorem product_graded_finrank (F : Linear.FiniteFiltration K V) (G : Linear.FiniteFiltration K W) (i : ℤ) :
    Module.finrank K ((product F G).Graded i) = Module.finrank K (F.Graded i) + Module.finrank K (G.Graded i) := by
  have h₀ := product_step_finrank F G i
  have h₁ := product_step_finrank F G (i + 1)
  have hF := F.graded_finrank_add i
  have hG := G.graded_finrank_add i
  have hFG := (product F G).graded_finrank_add i
  omega

theorem product_tH (F : Linear.FiniteFiltration K V) (G : Linear.FiniteFiltration K W) :
    (product F G).tH = F.tH + G.tH := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  rw [← finsum_add_distrib F.hodge_summand_finite_support G.hodge_summand_finite_support]
  congr 1
  funext i
  rw [product_graded_finrank, Nat.cast_add, mul_add]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProductFiltration.FiltrationTransport
